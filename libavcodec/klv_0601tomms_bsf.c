#include <float.h>

#include "avcodec.h"
#include "bsf.h"
/* Jagwire */
#include "bsf_internal.h"
/* Jagwire - End */
#include "put_bits.h"
#include "get_bits.h"
#include "internal.h"

#include "libavutil/log.h"
#include "libavutil/opt.h"
#include "libavutil/time.h"

#define MAX_KEYS_LOCAL_MMS 23
#define MAX_KEYS_SECURITY_MMS 9
#define MAX_KEYS_UAS_LS 108
#define MAX_KEYS_SECURITY_LS 24
#define TAG_ID_SECURITY_LS 48
#define MMS_TAG_SIZE 1
#define MMS_LENGTH_SIZE 1

typedef struct MMSData {
    int key;
    int key_length;
    int start_offset;
    int data_length;
	  uint8_t *data;
    int64_t last_sent;
    int64_t last_received;
} MMSData;

typedef struct MMSDefinition {
    int key;
    int max_length;
    int update_interval; /* Seconds */
} MMSDefinition;

/* Last updated from MISB ST 0902.8 */
static struct MMSDefinition localMmsInfo[] = {
    {2, 8, 0},     /* Precision Time Stamp */
    {3, 127, 10},  /* Mission ID */
    {5, 2, 0},     /* Platform Heading Angle */
    {6, 2, 0},     /* Platform Pitch Angle (Short) */
    {7, 2, 0},     /* Platform Roll Angle (Short) */
    {10, 127, 10}, /* Platform Designation */
    {11, 127, 10}, /* Image Source Sensor */
    {12, 127, 10}, /* Image Coordinate System */
    {13, 4, 0},    /* Sensor Latitude */
    {14, 4, 0},    /* Sensor Longitude */
    {15, 2, 0},    /* Sensor True Altitude (MSL) */
    {16, 2, 0},    /* Sensor Horizontal FoV */
    {17, 2, 0},    /* Sensor Vertical FoV */
    {18, 4, 0},    /* Sensor Relative Azimuth Angle */
    {19, 4, 0},    /* Sensor Relative Elevation Angle */
    {20, 4, 0},    /* Sensor Relative Roll Angle */
    {21, 4, 0},    /* Slant Range */
    {22, 2, 0},    /* Target Width */
    {23, 4, 0},    /* Frame Center Latitude */
    {24, 4, 0},    /* Frame Center Longitude */
    {25, 2, 0},    /* Frame Center Elevation (MSL) */
    {48, 1, 10},   /* Security Local Metadata Set */
    {65, 1, 0},    /* UAS Local Set Version */
    {94, 50, 10},  /* Motion Imagery Core Identifier */
};

static struct MMSDefinition securityMmsInfo[] = {
    {1, 1, 10},   /* Security Classification */
    {2, 1, 10},   /* Classifying Country & Releasing Instructions Country Coding Method */
    {3, 6, 10},   /* Classifying Country */
    {4, 40, 10},  /* Security-SCI/SHI Information */
    {5, 32, 10},  /* Caveats */
    {6, 40, 10},  /* Releasing Instructions */
    {12, 1, 10},  /* Object Country Coding Method */
    {13, 40, 10}, /* Object Country Codes */
    {22, 2, 10},  /* Security Metadata Version */
};

typedef struct MMSBSFContext {
    const AVClass *class;
    AVPacket in;
    int in_data_offset;
    AVPacket *out;
    int out_data_offset;
    MMSData *local_mms_data;
    MMSData *security_mms_data;
    uint8_t *process_data;
    int process_data_offset;
    int max_mms_length;
    float frame_delta;
    int64_t last_sent;
    int verify_checksum;
    float frame_rate;
} MMSBSFContext;

static const uint8_t LDS_KEY[] = {
    0x06, 0x0E, 0x2B, 0x34,
    0x02, 0x0B, 0x01, 0x01,
    0x0E, 0x01, 0x03, 0x01,
    0x01, 0x00, 0x00, 0x00
};
static struct MMSDefinition localMmsKeys[MAX_KEYS_UAS_LS];
static struct MMSDefinition securityMmsKeys[MAX_KEYS_SECURITY_LS];

static int find_0601_key(AVPacket *pkt, int *data_offset)
{
    int buf_idx = *data_offset;

    // Find start of next key
    while ((buf_idx + 15) < pkt->size &&
        (pkt->data[buf_idx] != LDS_KEY[0] ||
        pkt->data[buf_idx + 1] != LDS_KEY[1] ||
        pkt->data[buf_idx + 2] != LDS_KEY[2] ||
        pkt->data[buf_idx + 3] != LDS_KEY[3] ||
        pkt->data[buf_idx + 4] != LDS_KEY[4] ||
        pkt->data[buf_idx + 5] != LDS_KEY[5] ||
        pkt->data[buf_idx + 6] != LDS_KEY[6] ||
        pkt->data[buf_idx + 7] != LDS_KEY[7] ||
        pkt->data[buf_idx + 8] != LDS_KEY[8] ||
        pkt->data[buf_idx + 9] != LDS_KEY[9] ||
        pkt->data[buf_idx + 10] != LDS_KEY[10] ||
        pkt->data[buf_idx + 11] != LDS_KEY[11] ||
        pkt->data[buf_idx + 12] != LDS_KEY[12] ||
        pkt->data[buf_idx + 13] != LDS_KEY[13] ||
        pkt->data[buf_idx + 14] != LDS_KEY[14] ||
        pkt->data[buf_idx + 15] != LDS_KEY[15])) {
        buf_idx++;
    }
    
    if ((buf_idx + 16) < pkt->size) {
        *data_offset = buf_idx + 16;
        return 0;
    }

    return -1;
}

static int klv_decode_ber_length(AVPacket *pkt, int *data_offset, int *key_length)
{
    int buf_idx = *data_offset;
    int length = pkt->data[buf_idx] & 0xff;

    if (length & 0x80) { // long form
        int bytes_num = length & 0x7f;

        // SMPTE 379M 5.3.4 guarantee that bytes_num must not exceed 8 bytes
        // and must have enough buffer to decode length
        if ((buf_idx + bytes_num) >= pkt->size || bytes_num > 8) {
            return -1;
        }

        length = 0;
        while (bytes_num-- && buf_idx < pkt->size) {
            length = length << 8 | pkt->data[++buf_idx];
        }
    }

    buf_idx++;
    *data_offset = buf_idx;

    if (buf_idx < pkt->size) {
        *key_length = length;
        return 0;
    }

    return -1;
}

static int klv_decode_ber_oid_tag(AVPacket *pkt, int *packet_data_offset, int *tag_id)
{
    int buf_idx = *packet_data_offset;

    if (buf_idx >= pkt->size) {
      return -1;
    }

    // Decode tag that is BER-OID encoded
    if ((pkt->data[buf_idx] & 0x80) == 0) {
      *packet_data_offset = buf_idx + 1;
      *tag_id = pkt->data[buf_idx];
      return 0;
    }
    else
    {
        int ber_value;
        int decoded_ber_value = 0;
        int target_id_decoded = 0;

        do
        {
            decoded_ber_value <<= 7;
            if (buf_idx >= pkt->size) {
                return -1;
            }
            ber_value = pkt->data[buf_idx++] & 0xff;
            if ((ber_value & 0x80) == 0)
            {
                target_id_decoded = 1;
            }
            else
            {
                ber_value &= ~0x80;
            }
            decoded_ber_value |= ber_value;
        } while (!target_id_decoded);

        *packet_data_offset = buf_idx;
        *tag_id = decoded_ber_value;
        return 0;
    }
}

static unsigned short bcc16(uint8_t *buf, int len)
{
  unsigned short bcc = 0, i;

  for (i = 0; i < len; i++) {
      bcc += buf[i] << (8 * ((i + 1) % 2));
  }

  return bcc;
}

static int parseLocalSet(MMSBSFContext *s, int local_set_length, MMSDefinition *keys, int max_tag_id, int64_t received_time)
{
    AVPacket *in_pkt = &s->in;
    int tag_id = 0;
    int tag_data_length = 0;
    int data_available = 1;
    int ret, tag_offset_start;

    local_set_length += s->in_data_offset;

    while (data_available) {
        // Break if we have no more data
        if (s->in_data_offset >= local_set_length) {
            // If offset is larger than total buffer length then something is wrong
            if (s->in_data_offset > local_set_length) {
                av_log(s, AV_LOG_DEBUG,
                    "Current buffer offset exceeds LDS tag length, offset:%d length:%d\n",
                    s->in_data_offset, local_set_length);
                data_available = 0;
            }
            break;
        }

        tag_offset_start = s->in_data_offset;

        // Decode local set tag
        ret = klv_decode_ber_oid_tag(in_pkt, &s->in_data_offset, &tag_id);
        if (ret < 0) {
            av_log(s, AV_LOG_DEBUG, "Ran out of data decoding tag ID\n");
            return ret;
        }

        // Decode local set tag data length
        ret = klv_decode_ber_length(in_pkt, &s->in_data_offset, &tag_data_length);
        if (ret < 0) {
            av_log(s, AV_LOG_DEBUG,
                "Found incorrect tag length, tag:%d  length:%d\n",
                tag_id, tag_data_length);
            return ret;
        }

        // Validate the tag ID
        if (tag_id > max_tag_id) {
            av_log(s, AV_LOG_DEBUG, "Found invalid tag ID %d, skipping %d bytes\n",
                tag_id, tag_data_length);
            s->in_data_offset += tag_data_length;
            continue;
        }

        if (tag_id == TAG_ID_SECURITY_LS) {
            ret = parseLocalSet(s, tag_data_length, securityMmsKeys, 
                MAX_KEYS_SECURITY_LS, received_time);
            if (ret < 0) {
                data_available = 0;
            }
        }
        else
        {
            MMSData *mms_data = max_tag_id == MAX_KEYS_UAS_LS ?
                s->local_mms_data : s->security_mms_data;

            // Advance offset to end of data
            s->in_data_offset += tag_data_length;

            // Validate offset
            if (s->in_data_offset > in_pkt->size || s->in_data_offset < 0) {
                if (s->in_data_offset > in_pkt->size) {
                    av_log(s, AV_LOG_DEBUG, 
                        "Current buffer offset exceeds block length, offset:%d length:%d\n",
                        s->in_data_offset, in_pkt->size);
                }
                else {
                    av_log(s, AV_LOG_DEBUG, 
                        "Invalid buffer offset, offset:%d\n", s->in_data_offset);
                }
                return -1;
            }

            if (keys[tag_id].key > 0)
            {
                mms_data[tag_id].key = tag_id;
                mms_data[tag_id].start_offset = tag_offset_start;
                mms_data[tag_id].data_length = s->in_data_offset - tag_offset_start;
                mms_data[tag_id].key_length = tag_data_length;
                mms_data[tag_id].last_received = received_time;

                // Only tags with a slow update interval require possible data truncation.
                // So we malloc the space here for that operation.
                if (keys[tag_id].update_interval > 0 &&
                    mms_data[tag_id].data == NULL) {
                    mms_data[tag_id].data = (uint8_t *) av_malloc(
                        keys[tag_id].max_length + MMS_TAG_SIZE + MMS_LENGTH_SIZE);
                }
            }
        }
    }
    return data_available ? 0 : -1;
}

static int processLocalSet(MMSBSFContext *s, int max_tag_id, int64_t received_time)
{
    int mms_keys_offset = 0;
    int tag_id = 0;
    MMSData *mms_data = NULL;
    const MMSDefinition *mms_keys = NULL;
    int64_t current_time = av_gettime_relative();
    int have_local_set_key = 0;
    int sms_start = 0;

    if (max_tag_id == MAX_KEYS_UAS_LS) {
        s->process_data = (uint8_t *) av_mallocz(s->in.size);
        if (!s->process_data) {
            av_log(s, AV_LOG_ERROR, "Unable to allocate memory\n");
            return -1;
        }
        s->process_data_offset = 0;
        mms_data = s->local_mms_data;
        mms_keys = localMmsKeys;
    }
    else {
        mms_data = s->security_mms_data;
        mms_keys = securityMmsKeys;
    }

    while (mms_keys_offset <= max_tag_id) {
        tag_id = mms_keys[mms_keys_offset].key;

        if (tag_id == TAG_ID_SECURITY_LS) {
            processLocalSet(s, MAX_KEYS_SECURITY_LS, received_time);
        }
        else if (mms_data[tag_id].key > 0) { // A valid MMS tag
            // If the update interval has passed or data is available and 30
            // seconds has passed copy it to the output
            if ((current_time >= mms_data[tag_id].last_sent + (mms_keys[mms_keys_offset].update_interval * 1000000) &&
                mms_data[tag_id].last_received == received_time) ||
                (mms_keys[mms_keys_offset].update_interval > 0 && 
                mms_data[tag_id].data != NULL && 
                current_time >= mms_data[tag_id].last_sent + 30000000)) {
                uint8_t *tag_data_to_copy;

                // Add the security local set tag if we are processing it and
                // it has not already been added
                if (max_tag_id == MAX_KEYS_SECURITY_LS && !have_local_set_key) {
                    s->process_data[s->process_data_offset] = 48;
                    s->process_data_offset += 2;
                    sms_start = s->process_data_offset;
                    have_local_set_key = 1;
                }

                // Shorten the data length if it exceeds MMS max length
                if (mms_data[tag_id].key_length > mms_keys[mms_keys_offset].max_length) {
                    int length_offset = mms_data[tag_id].key_length -
                        mms_keys[mms_keys_offset].max_length;

                    mms_data[tag_id].data_length -= length_offset;
                    mms_data[tag_id].key_length -= length_offset;
                    //s->out->data[mms_data[tag_id].start_offset + MMS_LENGTH_SIZE] = mms_keys[mms_keys_offset].max_length;
                }

                if (mms_keys[mms_keys_offset].update_interval > 0 && mms_data[tag_id].data != NULL) {
                    // Refresh the MMS data if it was just updated
                    if (mms_data[tag_id].last_received == received_time) {
                        memcpy(mms_data[tag_id].data, &s->in.data[mms_data[tag_id].start_offset],
                            mms_data[tag_id].data_length);
                    }

                    // Assign the current MMS data
                    tag_data_to_copy = mms_data[tag_id].data;
                }
                else {
                    tag_data_to_copy = &s->in.data[mms_data[tag_id].start_offset];
                }

                memcpy(s->process_data + s->process_data_offset, tag_data_to_copy,
                        mms_data[tag_id].data_length);
                if (mms_data[tag_id].key_length != s->process_data[s->process_data_offset + MMS_TAG_SIZE]) {
                    s->process_data[s->process_data_offset + MMS_TAG_SIZE] = mms_data[tag_id].key_length;
                }
					
                s->process_data_offset += mms_data[tag_id].data_length;

                mms_data[tag_id].last_sent = current_time;
            }
        }
        mms_keys_offset++;
    }

    if (max_tag_id == MAX_KEYS_UAS_LS) {
        int length_offset = 0;
        unsigned short crc;

        s->process_data_offset += 4; // Add length for checksum

        // Copy the local set key
        memcpy(s->out->data, s->in.data, 16);
        length_offset += 16;

        // Copy the local set length
        if (s->process_data_offset <= 127) {
            s->out->data[length_offset++] = s->process_data_offset;
        }
        else {
            s->out->data[length_offset++] = 0x82;
            s->out->data[length_offset++] = s->process_data_offset >> 8;
            s->out->data[length_offset++] = s->process_data_offset & 0xff;
        }
        
        // Copy the local set data
        memcpy(s->out->data + length_offset, s->process_data, s->process_data_offset);
        s->process_data_offset += length_offset;
        s->out->size = s->process_data_offset;

        // Create the checsum tag
        s->out->data[s->process_data_offset - 4] = 1;
        s->out->data[s->process_data_offset - 3] = 2;
        crc = bcc16(s->out->data, s->out->size);
        s->out->data[s->process_data_offset - 2] = crc >> 8;
        s->out->data[s->process_data_offset - 1] = crc & 0xff;

        if (s->process_data) {
            av_freep(&s->process_data);
        }
    }
    else if (have_local_set_key) {
        // Set the security local set length
        s->process_data[sms_start - 1] = s->process_data_offset - sms_start;
    }

    return 0;
}

static int klv_0601tomms_init(AVBSFContext *ctx)
{
    MMSBSFContext *s = ctx->priv_data;
    int i, j;
    int ret = 0;

    s->last_sent = 0;

    if (s->frame_rate >= 1.0f) {
        s->frame_delta = 1.0f / s->frame_rate;
        av_log(s, AV_LOG_DEBUG, "frame_delta: %f\n", s->frame_delta);
    }

    for (i = 1, j = 0; i <= MAX_KEYS_UAS_LS && j < MAX_KEYS_LOCAL_MMS; i++) {
        if (localMmsInfo[j].key == i) {
            localMmsKeys[i] = localMmsInfo[j];
            s->max_mms_length += localMmsInfo[j].max_length;
            j++;
        }
    }
    
    for (i = 1, j = 0; i <= MAX_KEYS_SECURITY_LS && j < MAX_KEYS_SECURITY_MMS; i++) {
        if (securityMmsInfo[j].key == i) {
            securityMmsKeys[i] = securityMmsInfo[j];
            s->max_mms_length += securityMmsInfo[j].max_length;
            j++;
        }
    }

    s->local_mms_data = (MMSData *) av_mallocz(sizeof(MMSData) * MAX_KEYS_UAS_LS + 1);
    if (!s->local_mms_data) {
        ret = AVERROR(ENOMEM);
        av_log(s, AV_LOG_ERROR, "Error initializing UAS Local Set tag data!\n");
        return ret;
    }

    s->security_mms_data = (MMSData *) av_mallocz(sizeof(MMSData) * MAX_KEYS_SECURITY_LS + 1);
    if (!s->security_mms_data) {
        ret = AVERROR(ENOMEM);
        av_log(s, AV_LOG_ERROR, "Error initializing Security Local Set tag data!\n");
        return ret;
    }

    return ret;
}

/**
 * This filter reduces a MISB ST 0601 metadata stream to a MISB ST 0902 MIMMS
 * metadata stream.
 */
static int klv_0601tomms_filter(AVBSFContext *ctx, AVPacket *out)
{
    MMSBSFContext *s = ctx->priv_data;

    AVPacket *in = &s->in;
    static int64_t received_time = 0;
    int64_t current_time;
    int data_offset = 0;
    int local_set_length;
    int ret = 0;

    ret = ff_bsf_get_packet_ref(ctx, in);
    if (ret < 0) {
        return ret;
    }

    if (s->frame_rate >= 1.0f && s->last_sent) {
        float sent_delta;
        current_time = av_gettime_relative();
        sent_delta = (float) (current_time - s->last_sent) / 1000000.0f;
        av_log(s, AV_LOG_DEBUG, "sent_delta:%f frame_delta:%f\n", sent_delta, s->frame_delta);
        if (sent_delta < s->frame_delta) {
            ret = av_new_packet(out, 0);
            if (!ret) {
                ret = av_packet_copy_props(out, in);
                if (ret < 0) {
                    av_packet_unref(out);
                }
            }
            av_packet_unref(in);
            return ret;
        }
    }

    // Find the start offset of the MISB ST 0601 local set
    ret = find_0601_key(in, &data_offset);
    if (ret < 0) {
        av_log(s, AV_LOG_DEBUG, "MISB ST 0601 local set key not found\n");
        goto fail;
    }
    
    // Decode MISB ST 0601 length
    ret = klv_decode_ber_length(in, &data_offset, &local_set_length);
    if (ret < 0) {
        av_log(s, AV_LOG_DEBUG, "MISB ST 0601 local set length not available or corrupt\n");
        goto fail;
    }

    // Verify MISB ST 0601 data length is available
    if (in->size < (data_offset + local_set_length)) {
        av_log(s, AV_LOG_DEBUG, "MISB ST 0601 data missing, expected:%d bytes actual:%d bytes\n",
            local_set_length, in->size - data_offset);
        ret = -1;
        goto fail;
    }

    // Verify checksum
    if (s->verify_checksum) {
        unsigned short calculated_crc = bcc16(in->data, in->size - 2);
        unsigned short block_crc = ((in->data[in->size - 2] & 0xff) << 8) |
            (in->data[in->size - 1] & 0xff);
        if (calculated_crc != block_crc) {
            av_log(s, AV_LOG_DEBUG, "MIST ST 0601 CRC mismatch detected.\n");
            ret = -1;
            goto fail;
        }
    }

    // Copy input packet
    ret = av_new_packet(out, s->max_mms_length);
    if (ret < 0) {
        goto fail;
    }

    ret = av_packet_copy_props(out, in);
    if (ret < 0) {
        av_packet_unref(out);
        goto fail;
    }

    s->in_data_offset = data_offset;
    s->out = out;
    s->out_data_offset = 0;
    received_time++;
    
    ret = parseLocalSet(s, local_set_length, localMmsKeys, MAX_KEYS_UAS_LS, received_time); 
    if (ret < 0) {
        av_log(s, AV_LOG_DEBUG,
            "Parsing failed. MISB ST 0601 data will not be converted.\n");
        av_packet_unref(out);
        goto fail;
    }

    ret = processLocalSet(s, MAX_KEYS_UAS_LS, received_time);
    if (ret < 0) {
        av_log(s, AV_LOG_DEBUG, "Processing MISB ST 0601 to MMS failed.\n");
        av_packet_unref(out);
        goto fail;
    }

fail:
    if (ret < 0) {
        av_packet_move_ref(out, in);
    }
    
    av_packet_unref(in);
    s->last_sent = av_gettime_relative();

    return 0;
}

static void klv_0601tomms_close(AVBSFContext *ctx)
{
    MMSBSFContext *s = ctx->priv_data;

    if (s->local_mms_data) {
        av_freep(&s->local_mms_data);
    }

    if (s->security_mms_data) {
        av_freep(&s->security_mms_data);
    }
}

static const enum AVCodecID codec_ids[] = {
    AV_CODEC_ID_SMPTE_KLV, AV_CODEC_ID_NONE,
};

#define OFFSET(x) offsetof(MMSBSFContext, x)
#define FLAGS (AV_OPT_FLAG_DATA_PARAM|AV_OPT_FLAG_BSF_PARAM)
static const AVOption options[] = {
  { "crc", "Verify the checksum of incoming MISB ST 0601 metadata", OFFSET(verify_checksum), AV_OPT_TYPE_BOOL, {.i64=1}, 0, 1, FLAGS },
  { "rate", "Sets the rate of the outgoing data in frames per second", OFFSET(frame_rate), AV_OPT_TYPE_FLOAT, {.dbl=FLT_MIN}, FLT_MIN, 60, FLAGS },
  { NULL }
};

static const AVClass klv_0601tomms_class = {
    .class_name = "klv_0601tomms",
    .item_name  = av_default_item_name,
    .option     = options,
    .version    = LIBAVUTIL_VERSION_INT,
};

const FFBitStreamFilter ff_klv_0601tomms_bsf = {
    .p.name         = "klv_0601tomms",
    .p.codec_ids    = codec_ids,
    .p.priv_class   = &klv_0601tomms_class,
    .priv_data_size = sizeof(MMSBSFContext),
    .init           = &klv_0601tomms_init,
    .close          = &klv_0601tomms_close,
    .filter         = &klv_0601tomms_filter,
};
