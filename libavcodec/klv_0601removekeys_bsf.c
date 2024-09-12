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
/* Jagwire */
#include "libavutil/mem.h"
/* Jagwire - End */

#include <unistd.h>

#define LDS_KEYS_END 180
#define CHECKSUM_LENGTH 4
#define KEY_LENGTH 16

typedef struct {
    int i_tag_id;
    int i_data_start_offset;
    int i_data_length;
    int i_payload_length;
    uint8_t *data;
} KLVTag;

typedef struct {
    int i_remove_tag;
} remove_definition_t;

typedef struct {
    const AVClass *class;
    AVPacket in;
    int in_data_offset;
    AVPacket *out;
    int out_data_offset;
    KLVTag *lds_data;
    uint8_t *process_data;
    int process_data_offset;
    uint64_t frame_delta;
    uint64_t st0601_last_sent;
    uint64_t other_last_sent;
    int verify_checksum;
    float frame_rate;
} BSFContext;

static const uint8_t LDS_KEY[] = {
    0x06, 0x0E, 0x2B, 0x34,
    0x02, 0x0B, 0x01, 0x01,
    0x0E, 0x01, 0x03, 0x01,
    0x01, 0x00, 0x00, 0x00
};

remove_definition_t remove_keys[LDS_KEYS_END];

int keys_loaded = 0;

static int loadRemoveLDSKeys(AVBSFContext *ctx)
{
    BSFContext *s = ctx->priv_data;
    FILE *keys_fd = NULL;
    int ret = 0;
    char buf[256] = {0};

    ssize_t length = readlink("/proc/self/exe", buf, 240);
    if (length != -1)
    {
      char *offset = strrchr( buf,  '/');
      if( offset )
        strcpy(++offset, "etc/remove_keys.conf");
    }

    keys_fd = fopen(buf, "r");
    if( keys_fd )
    {
        int i_tag_id = 0;

        while( fgets(buf, 250, keys_fd) != NULL )
        {
            if( buf[0] != '#' && buf[0] != '\n' )
            {
                i_tag_id = strtol(buf, NULL, 0);
                remove_keys[i_tag_id].i_remove_tag = i_tag_id;
            }
        }
        fclose(keys_fd);
    }
    else
    {
        av_log(s, AV_LOG_ERROR, "0601 key removal config file not found. Removing all keys: %s\n", buf);
        ret = 1;
    }

    return ret;
}

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
    
    if ((buf_idx + KEY_LENGTH) < pkt->size) {
        *data_offset = buf_idx + KEY_LENGTH;
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

static int parseLocalSet(BSFContext *s, int local_set_length)
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
        if (tag_id > LDS_KEYS_END) {
            av_log(s, AV_LOG_DEBUG, "Found invalid tag ID %d, skipping %d bytes\n",
                tag_id, tag_data_length);
            s->in_data_offset += tag_data_length;
            continue;
        }

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

        if (remove_keys[tag_id].i_remove_tag == 0)
        {
            s->lds_data[tag_id].i_tag_id = tag_id;
            s->lds_data[tag_id].i_data_start_offset = tag_offset_start;
            s->lds_data[tag_id].i_data_length = s->in_data_offset - tag_offset_start;
            s->lds_data[tag_id].i_payload_length = tag_data_length;
        }
    }
    return data_available ? 0 : -1;
}

static int processLocalSet(BSFContext *s)
{
    int i_tag_offset = 2;//start check after checksum and timestamp since they are required

    s->process_data = (uint8_t *) av_mallocz(s->in.size);
    if (!s->process_data) {
        av_log(s, AV_LOG_ERROR, "Unable to allocate memory\n");
        return -1;
    }
    s->process_data_offset = 0;
    
    /*If keys failed to load don't copy any data to the output
     *other than the 0601 key and checksum. This is dome to be sure
     *we don't accidentally pass data we shouldn't */
    if(!keys_loaded)
      i_tag_offset = LDS_KEYS_END;

    while (i_tag_offset < LDS_KEYS_END) {

        if (s->lds_data[i_tag_offset].i_tag_id > 0) {

            uint8_t *p_data = &s->in.data[s->lds_data[i_tag_offset].i_data_start_offset];

            memcpy(s->process_data + s->process_data_offset, p_data, s->lds_data[i_tag_offset].i_data_length);

            s->process_data_offset += s->lds_data[i_tag_offset].i_data_length;
        }
        i_tag_offset++;
    }

    if (i_tag_offset == LDS_KEYS_END) {
        int length_offset = 0;
        unsigned short crc;

        s->process_data_offset += CHECKSUM_LENGTH; // Add length for checksum

        // Copy the local set key
        memcpy(s->out->data, s->in.data, KEY_LENGTH);
        length_offset += KEY_LENGTH;

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

        // Create the checksum tag
        s->out->data[s->process_data_offset - 4] = 1;
        s->out->data[s->process_data_offset - 3] = 2;
        crc = bcc16(s->out->data, s->out->size);
        s->out->data[s->process_data_offset - 2] = crc >> 8;
        s->out->data[s->process_data_offset - 1] = crc & 0xff;

        if (s->process_data) {
            av_freep(&s->process_data);
        }
    }

    return 0;
}

static int klv_0601removekeys_init(AVBSFContext *ctx)
{
    BSFContext *s = ctx->priv_data;
    int ret = 0;

    s->st0601_last_sent = 0;
    s->other_last_sent = 0;

    if (s->frame_rate >= 1.0f) {
        s->frame_delta = 90000/s->frame_rate;
        av_log(s, AV_LOG_DEBUG, "frame_delta: %lu\n", s->frame_delta);
    }

    s->lds_data = (KLVTag *) av_mallocz(sizeof(KLVTag) * LDS_KEYS_END);
    if (!s->lds_data) {
        ret = AVERROR(ENOMEM);
        av_log(s, AV_LOG_ERROR, "Error initializing MISB 0601 Local Set tag data!\n");
        return ret;
    }

    keys_loaded = !loadRemoveLDSKeys(ctx);

    return ret;
}

/**
 * This filter removes configured keys from a MISB ST 0601 metadata stream.
 * Non 0601 data is passed unaltered
 */
static int klv_0601removekeys_filter(AVBSFContext *ctx, AVPacket *out)
{
    BSFContext *s = ctx->priv_data;

    AVPacket *in = &s->in;
    int data_offset = 0;
    int local_set_length;
    int ret = 0;

    ret = ff_bsf_get_packet_ref(ctx, in);
    if (ret < 0) {
        return ret;
    }

    // Find the start offset of the MISB 0601 local set
    ret = find_0601_key(in, &data_offset);
    if (ret < 0) {
        //If we don't find 0601 but do find other data, pass it on as is.
        if (s->frame_rate >= 1.0f) {
            uint64_t sent_delta;
            sent_delta = in->dts - s->other_last_sent;
            if (sent_delta < s->frame_delta) {
                av_packet_unref(in);
                return 0;
            }
        }
        av_log(s, AV_LOG_DEBUG, "MISB 0601 local set key not found. Passing data unaltered\n");
        s->other_last_sent = in->dts;
        av_packet_move_ref(out, in);
        av_packet_unref(in);
        return 0;
    }

    if (s->frame_rate >= 1.0f && s->st0601_last_sent) {
        uint64_t sent_delta;
        sent_delta = in->dts - s->st0601_last_sent;
        if (sent_delta < s->frame_delta) {
            av_packet_unref(in);
            return ret;
        }
    }

    // Decode MISB ST 0601 length
    ret = klv_decode_ber_length(in, &data_offset, &local_set_length);
    if (ret < 0) {
        av_log(s, AV_LOG_DEBUG, "MISB 0601 local set length not available or corrupt\n");
        goto fail;
    }

    // Verify MISB ST 0601 data length is available
    if (in->size < (data_offset + local_set_length)) {
        av_log(s, AV_LOG_DEBUG, "MISB 0601 data missing, expected:%d bytes actual:%d bytes\n",
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
            av_log(s, AV_LOG_DEBUG, "MISB 0601 CRC mismatch detected.\n");
            ret = -1;
            goto fail;
        }
    }

    // Copy input packet
    ret = av_new_packet(out, in->size);
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
    memset(s->lds_data, 0, sizeof(KLVTag) * LDS_KEYS_END);

    ret = parseLocalSet(s, local_set_length); 
    if (ret < 0) {
        av_log(s, AV_LOG_DEBUG,
            "Parsing failed for key removal. MISB 0601 data will be dropped.\n");
        av_packet_unref(out);
        goto fail;
    }

    ret = processLocalSet(s);
    if (ret < 0) {
        av_log(s, AV_LOG_DEBUG, "Processing failed for key removal. MISB 0601 data will be dropped.\n");
        av_packet_unref(out);
        goto fail;
    }

fail:    
    s->st0601_last_sent = in->dts;
    av_packet_unref(in);

    return 0;
}

static void klv_0601removekeys_close(AVBSFContext *ctx)
{
    BSFContext *s = ctx->priv_data;

    if (s->lds_data) {
        av_freep(&s->lds_data);
    }
}

static const enum AVCodecID codec_ids[] = {
    AV_CODEC_ID_SMPTE_KLV, AV_CODEC_ID_NONE,
};

#define OFFSET(x) offsetof(BSFContext, x)
#define FLAGS (AV_OPT_FLAG_DATA_PARAM|AV_OPT_FLAG_BSF_PARAM)
static const AVOption options[] = {
  { "crc", "Verify the checksum of incoming MISB 0601 metadata", OFFSET(verify_checksum), AV_OPT_TYPE_BOOL, {.i64=1}, 0, 1, FLAGS },
  { "rate", "Sets the rate of the outgoing data in frames per second", OFFSET(frame_rate), AV_OPT_TYPE_FLOAT, {.dbl=FLT_MIN}, FLT_MIN, 60, FLAGS },
  { NULL }
};

static const AVClass klv_0601removekeys_class = {
    .class_name = "klv_0601removekeys",
    .item_name  = av_default_item_name,
    .option     = options,
    .version    = LIBAVUTIL_VERSION_INT,
};

const FFBitStreamFilter ff_klv_0601removekeys_bsf = {
    .p.name         = "klv_0601removekeys",
    .p.codec_ids    = codec_ids,
    .p.priv_class   = &klv_0601removekeys_class,
    .priv_data_size = sizeof(BSFContext),
    .init           = &klv_0601removekeys_init,
    .close          = &klv_0601removekeys_close,
    .filter         = &klv_0601removekeys_filter,
};
