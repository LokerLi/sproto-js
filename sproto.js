var Sproto = {
    createNew: function (binsch) {
        var sproto = {};
        var result = new Object();
        var __session = new Array();
        var enbuffer;
        var SPROTO_TARRAY = 0x80;
        var SPROTO_TINTEGER = 0;
        var SPROTO_TBOOLEAN = 1;
        var SPROTO_TSTRING = 2;
        var SPROTO_TSTRUCT = 3;
        var SIZEOF_LENGTH = 4;
        var SIZEOF_HEADER = 2;
        var SIZEOF_FIELD = 2;
        var ENCODE_DEEPLEVEL = 64;
        var SPROTO_REQUEST = 0;
        var SPROTO_RESPONSE = 1;

        function array_concat(a1, a2) {
            var b = new Array();
            for (var i = 0; i < a1.sz; i++) {
                b[i] = a1.buf[i];
            }
            for (var j = a1.sz; j < a1.sz + a2.sz; j++) {
                b[j] = a2.buf[j - a1.sz];
            }
            return { buf: b, sz: a1.sz + a2.sz };
        }
        function toword(stream) {
            return v = (stream[0] & 0xff) | (stream[1] & 0xff) << 8;
        }
        function todword(stream) {
            return (stream[0] & 0xff) | (stream[1] & 0xff) << 8 | (stream[2] & 0xff) << 16 | (stream[3] & 0xff) << 24;
        }
        function count_array(stream) {
            var length = todword(stream);
            var n = 0;
            stream = stream.slice(SIZEOF_LENGTH);
            while (length > 0) {
                var nsz;
                if (length < SIZEOF_LENGTH) {
                    return -1;
                }
                nsz = todword(stream);
                nsz += SIZEOF_LENGTH;
                if (nsz > length) {
                    return -1;
                }
                ++n;
                stream = stream.slice(nsz);
                length -= nsz;
            }
            return n;
        }
        function struct_field(stream, sz) {
            var field, fn, header, i;
            if (sz < SIZEOF_LENGTH) {
                return -1;
            }
            fn = toword(stream);
            header = SIZEOF_HEADER + SIZEOF_FIELD * fn;
            if (sz < header) {
                return -1;
            }
            field = stream.slice(SIZEOF_HEADER);
            sz -= header;
            stream = stream.slice(header);
            for (i = 0; i < fn; i++) {
                var value = toword(field.slice(i * SIZEOF_FIELD + SIZEOF_HEADER));
                var dsz;
                if (value != 0) {
                    continue;
                }
                if (sz < SIZEOF_LENGTH) {
                    return -1;
                }
                dsz = todword(stream);
                if (sz < SIZEOF_LENGTH + dsz) {
                    return -1;
                }
                stream = stream.slice(SIZEOF_LENGTH + dsz);
                sz -= SIZEOF_LENGTH + dsz;
            }
            return fn;
        }
        function import_string(stream) {
            var str = "";
            arr = stream.slice(SIZEOF_LENGTH, SIZEOF_LENGTH + todword(stream));
            for (var i = 0; i < arr.length; i++) {
                str += String.fromCharCode(arr[i]);
            }
            return str;
        }
        function import_field(f, stream) {
            var sz, result, fn, i;
            var array = 0;
            var tag = -1;
            f.tag = -1;
            f.type = -1;
            f.name = null;
            f.st = null;

            sz = todword(stream);
            stream = stream.slice(SIZEOF_LENGTH);
            result = stream.slice(sz);
            fn = struct_field(stream, sz);
            if (fn < 0) {
                return null;
            }
            stream = stream.slice(SIZEOF_HEADER);
            for (i = 0; i < fn; i++) {
                var value;
                ++tag;
                value = toword(stream.slice(SIZEOF_FIELD * i));
                if (value & 1 != 0) {
                    tag += Math.floor(value / 2);
                    continue;
                }
                if (tag == 0) {
                    if (value != 0) {
                        return null;
                    }
                    f.name = import_string(stream.slice(fn * SIZEOF_FIELD));
                    continue;
                }
                if (value == 0) {
                    return null;
                }
                value = Math.floor(value / 2) - 1;
                switch (tag) {
                    case 1:
                        if (value >= SPROTO_TSTRUCT) {
                            return null;
                        }
                        f.type = value;
                        break;
                    case 2:
                        if (value >= sproto.type_n) {
                            return null;
                        }
                        if (f.type >= 0) {
                            return null;
                        }
                        f.type = SPROTO_TSTRUCT;
                        f.st = value;
                        break;
                    case 3:
                        f.tag = value;
                        break;
                    case 4:
                        if (value != 0) {
                            array = SPROTO_TARRAY;
                        }
                        break;
                    default:
                        return null;
                }
            }
            if (f.tag < 0 || f.type < 0 || f.name == null) {
                return null;
            }
            f.type |= array;
            return result;
        }
        function import_type(t, stream) {
            var result, i, fn, n, maxn, last;
            var sz = todword(stream);
            stream = stream.slice(SIZEOF_LENGTH);
            result = stream.slice(sz);
            fn = struct_field(stream, sz);
            if (fn <= 0 || fn > 2) {
                return null;
            }
            for (i = 0; i < fn * SIZEOF_FIELD; i += SIZEOF_FIELD) {
                var v = toword(stream.slice(SIZEOF_HEADER + i));
                if (v != 0) {
                    return null;
                }
            }
            stream = stream.slice(SIZEOF_HEADER + fn * SIZEOF_FIELD);
            t.name = import_string(stream);
            if (fn == 1) {
                return result;
            }
            stream = stream.slice(todword(stream) + SIZEOF_LENGTH);
            n = count_array(stream);
            if (n < 0) {
                return null;
            }
            stream = stream.slice(SIZEOF_LENGTH);
            maxn = n;
            last = -1;
            t.n = n;
            t.f = new Array();
            for (i = 0; i < n; i++) {
                var tag;
                t.f[i] = new Object();
                var f = t.f[i];
                stream = import_field(f, stream);
                if (stream == null) {
                    return null;
                }
                tag = f.tag;
                if (tag < last) {
                    return null;
                }
                if (tag > last + 1) {
                    ++maxn;
                }
                last = tag;
            }
            t.maxn = maxn;
            t.base = t.f[0].tag;
            n = t.f[n - 1].tag - t.base + 1;
            if (n != t.n) {
                t.base = -1;
            }
            return result;
        }
        function import_protocol(p, stream) {
            var result, sz, fn, i, tag;
            sz = todword(stream);
            stream = stream.slice(SIZEOF_LENGTH);
            result = stream.slice(sz);
            fn = struct_field(stream, sz);
            stream = stream.slice(SIZEOF_HEADER);
            p.name = null;
            p.tag = -1;
            p.p = new Array();
            p.p[SPROTO_REQUEST] = null;
            p.p[SPROTO_RESPONSE] = null;
            tag = 0;
            for (i = 0; i < fn; i++ , tag++) {
                var value = toword(stream.slice(SIZEOF_FIELD * i));
                if (value & 1) {
                    tag += (value - 1) / 2;
                    continue;
                }
                value = value / 2 - 1;
                switch (i) {
                    case 0:
                        if (value != -1) {
                            return null;
                        }
                        p.name = import_string(stream.slice(SIZEOF_FIELD * fn));
                        break;
                    case 1:
                        if (value < 0) {
                            return null;
                        }
                        p.tag = value;
                        break;
                    case 2:
                        if (value < 0 || value >= sproto.type_n) {
                            return null;
                        }
                        p.p[SPROTO_REQUEST] = sproto.type[value];
                        break;
                    case 3:
                        if (value < 0 || value >= sproto.type_n) {
                            return null;
                        }
                        p.p[SPROTO_RESPONSE] = sproto.type[value];
                        break;
                    default:
                        return null;
                }
            }
            if (p.name == null || p.tag < 0) {
                return null;
            }
            return result;
        }
        function create_from_bundle(stream, sz) {
            var conetnt, typedata, protocoldata;
            var fn = struct_field(stream, sz);
            var i;
            if (fn < 0) {
                return null;
            }
            stream = stream.slice(SIZEOF_HEADER);
            content = stream.slice(fn * SIZEOF_FIELD);

            for (i = 0; i < fn; i++) {
                var value = toword(stream.slice(i * SIZEOF_FIELD));
                var n;
                if (value != 0) {
                    return null;
                }
                n = count_array(content);
                if (n < 0) {
                    return null;
                }
                if (i == 0) {
                    typedata = content.slice(SIZEOF_LENGTH);
                    sproto.type_n = n;
                    sproto.type = new Array();
                } else {
                    protocoldata = content.slice(SIZEOF_LENGTH);
                    sproto.protocol_n = n;
                    sproto.proto = new Array();
                }
                content = content.slice(todword(content) + SIZEOF_LENGTH);
            }
            for (i = 0; i < sproto.type_n; i++) {
                sproto.type[i] = new Object();
                typedata = import_type(sproto.type[i], typedata);
                if (typedata == null) {
                    return null;
                }
            }
            for (i = 0; i < sproto.protocol_n; i++) {
                sproto.proto[i] = new Object();
                protocoldata = import_protocol(sproto.proto[i], protocoldata);
                if (protocoldata == null) {
                    return null;
                }
            }
            return sproto;
        }

        function decode_array_object(cb, args, stream, sz) {
            var hsz;
            var index = 1;
            while (sz > 0) {
                if (sz < SIZEOF_LENGTH) {
                    return -1;
                }
                hsz = todword(stream);
                stream = stream.slice(SIZEOF_LENGTH);
                sz -= SIZEOF_LENGTH;
                if (hsz > sz) {
                    return -1;
                }
                args.index = index;
                args.value = stream;
                args.length = hsz;
                if (cb(args) != 0) {
                    return -1;
                }
                sz -= hsz;
                stream = stream.slice(hsz);
                ++index;
            }
            return 0;
        }
        function decode_array(cb, args, stream) {
            var sz = todword(stream);
            var type = args.type;
            var i;
            stream = stream.slice(SIZEOF_LENGTH);
            switch (type) {
                case SPROTO_TINTEGER: {
                    var len;
                    if (sz < 1) {
                        return -1;
                    }
                    len = stream[0];
                    stream = stream.slice(1);
                    --sz;
                    if (len == 4) {
                        if (sz % 4 != 0) {
                            return -1;
                        }
                        for (i = 0; i < Math.floor(sz / 4); i++) {
                            var value = todword(stream.slice(i * 4));
                            args.index = i + 1;
                            args.value = value;
                            args.length = 8;
                            cb(args);
                        }
                    } else {
                        alert("only support 4 bytes integer")
                        return -1;
                    }
                    break;
                }
                case SPROTO_TBOOLEAN:
                    for (i = 0; i < sz; i++) {
                        var value = stream[i];
                        args.index = i + 1;
                        args.value = value;
                        args.length = 8;
                        cb(args);
                    }
                    break;
                case SPROTO_TSTRING:
                case SPROTO_TSTRUCT:
                    return decode_array_object(cb, args, stream, sz);
                default:
                    return -1;
            }
            return 0;
        }
        function findtag(st, tag) {
            var begin, end;
            if (st.base >= 0) {
                tag -= st.base;
                if (tag < 0 || tag >= st.n) {
                    return null;
                }
                return st.f[tag];
            }
            begin = 0;
            end = st.n;
            while (begin < end) {
                var mid = (begin + end) / 2;
                var f = st.f[mid];
                var t = f.tag;
                if (t == tag) {
                    return f;
                }
                if (tag > t) {
                    begin = mid + 1;
                } else {
                    end = mid;
                }
            }
            return null;
        }
        function sproto_type(typename) {
            var i;
            for (i = 0; i < sproto.type_n; i++) {
                if (typeof typename == "string") { //modified by zmd typename类型不固定
                    if (typename == sproto.type[i].name) {
                        return sproto.type[i];
                    }
                }
                if (typeof typename == "object") { //modified by zmd typename类型不固定
                    if (typename == sproto.type[i]) {
                        return sproto.type[i];
                    }
                }
            }
            return null;
        }
        function sproto_protoquery_name(name) {
            for (var i = 0; i < sproto.protocol_n; i++) {
                if (sproto.proto[i].name == name) {
                    return sproto.proto[i];
                }
            }
            return null;
        }
        function sproto_protoquery(proto, what) {
            if (what < 0 || what > 1) {
                return null;
            }
            var begin, end, p;
            p = null;
            begin = 0;
            end = sproto.protocol_n;
            while (begin < end) {
                var mid = (begin + end) / 2;
                mid = parseInt(mid); //modified by zmd mid 有可能是0.5
                var t = sproto.proto[mid].tag;
                if (t == proto) {
                    p = sproto.proto[mid];
                }
                if (proto > t) {
                    begin = mid + 1;
                } else {
                    end = mid;
                }
                if (p != null) {
                    return p;//modified by zmd 返回的p要用到.p属性，所以需要返回p不是p.p[what]
                    // return p.p[what];
                }
            }
            return null;
        }
        function sproto_decode(st, data, size, cb, ud) {
            var args = new Object();
            var total = size;
            var stream, datastream, fn, i, tag;
            if (size < SIZEOF_HEADER) {
                return -1;
            }
            stream = data.slice(0);
            fn = toword(stream);
            stream = stream.slice(SIZEOF_HEADER);
            size -= SIZEOF_HEADER;
            if (size < fn * SIZEOF_FIELD) {
                return -1;
            }
            datastream = stream.slice(fn * SIZEOF_FIELD);
            size -= fn * SIZEOF_FIELD;
            args.ud = ud;

            tag = -1;
            for (i = 0; i < fn; i++) {
                var currentdata;
                var f;
                var value = toword(stream.slice(i * SIZEOF_FIELD));
                ++tag;
                if (value & 1 != 0) {
                    tag += Math.floor(value / 2);
                    continue;
                }
                value = Math.floor(value / 2) - 1;
                currentdata = datastream.slice(0);
                if (value < 0) {
                    var sz;
                    if (size < SIZEOF_LENGTH) {
                        return -1;
                    }
                    sz = todword(datastream);
                    if (size < sz + SIZEOF_LENGTH) {
                        return -1;
                    }
                    datastream = datastream.slice(sz + SIZEOF_LENGTH);
                    size -= sz + SIZEOF_LENGTH;
                }
                f = findtag(st, tag);
                if (f == null) {
                    continue;
                }
                args.tagname = f.name;
                args.tagid = f.tag;
                args.type = f.type & ~SPROTO_TARRAY;
                if (f.st != null) {
                    args.subtype = sproto.type[f.st];
                } else {
                    args.subtype = null;
                }
                args.index = 0;
                if (value < 0) {
                    var limitV = f.type & SPROTO_TARRAY; //如果f.type >= 0x80 则不执行数组解析 还不明白为什么
                    if (limitV != 0) { //modified by zmd  f.type & SPROTO_TARRAY != 0 一直是0 导致数组类型的进不来| 也就是value < 0的时候有问题| 有可能是js位运算执行有问题
                        if (decode_array(cb, args, currentdata) != 0) {
                            return -1;
                        }
                    } else {
                        switch (f.type) {
                            case SPROTO_TINTEGER: {
                                var sz = todword(currentdata);
                                if (sz == 4) {
                                    var v = todword(currentdata.slice(SIZEOF_LENGTH));
                                    args.value = v;
                                    args.length = 4;
                                    cb(args);
                                } else {
                                    alert("only support 32bit integer");
                                    return -1;
                                }
                                break;
                            }
                            case SPROTO_TSTRING:
                            case SPROTO_TSTRUCT: {
                                var sz = todword(currentdata);
                                args.value = currentdata.slice(SIZEOF_LENGTH);
                                args.length = sz;
                                if (cb(args) != 0) {
                                    return -1;
                                }
                                break;
                            }
                            default:
                                return -1;
                        }
                    }
                } else if (f.type != SPROTO_TINTEGER && f.type != SPROTO_TBOOLEAN) {
                    return -1;
                } else {
                    var v = value;
                    args.value = v;
                    args.length = 8;
                    cb(args);
                }
            }
            return total - size;
        }
        function decode(args) {
            var self = args.ud;
            var value;
            if (self.deep >= ENCODE_DEEPLEVEL) {
                alert("The table is too deep");
            }
            if (args.index > 0) {
                if (args.tagname != self.array_tag) {
                    self.array_tag = args.tagname;
                    self.result[args.tagname] = new Array();
                }
            }
            switch (args.type) {
                case SPROTO_TINTEGER:
                case SPROTO_TBOOLEAN:
                    value = args.value;
                    break;
                case SPROTO_TSTRING:
                    value = ""
                    for (var i = 0; i < args.length; i++) {
                        value += String.fromCharCode(args.value[i]);
                    }
                    break;
                case SPROTO_TSTRUCT:
                    var sub, r;
                    sub = new Object();
                    sub.deep = self.deep + 1;
                    sub.array_tag = null;
                    sub.result = new Object();
                    r = sproto_decode(args.subtype, args.value, args.length, decode, sub);
                    if (r < 0 || r != args.length) {
                        return r;
                    }
                    value = sub.result;
                    break;
                default:
                    alert("invalid type");
            }
            if (args.index > 0) {
                self.result[args.tagname][args.index - 1] = value; //modified by zmd index -1是因为 index > 0 才是数组
            } else {
                self.result[args.tagname] = value;
            }
            return 0;
        }
        function sproto_encode(type, buffer_idx, cb, ud) {
            var args = new Object();
            var header_idx = buffer_idx;
            var data_idx = buffer_idx;
            var st = type;
            var header_sz = SIZEOF_HEADER + st.maxn * SIZEOF_FIELD;
            var i, index, lasttag, datasz;


            function fill_size(data_idx, sz) {
                enbuffer[data_idx] = sz & 0xff;
                enbuffer[data_idx + 1] = (sz >> 8) & 0xff;
                enbuffer[data_idx + 2] = (sz >> 16) & 0xff;
                enbuffer[data_idx + 3] = (sz >> 24) & 0xff;
                return sz + SIZEOF_LENGTH;
            }
            function encode_integer(v, data_idx) {
                enbuffer[data_idx + 4] = v & 0xff;
                enbuffer[data_idx + 5] = (v >>> 8) & 0xff;
                enbuffer[data_idx + 6] = (v >>> 16) & 0xff;
                enbuffer[data_idx + 7] = (v >>> 24) & 0xff;
                return fill_size(data_idx, 4);
            }
            function encode_object(cb, args, data_idx) {
                var sz;
                args.value = data_idx + SIZEOF_LENGTH;
                // args.length = size - SIZEOF_LENGTH;
                sz = cb(args);
                if (sz <= 0) {
                    return sz;
                }
                if (args.type == SPROTO_TSTRING) {
                    --sz;
                }
                return fill_size(data_idx, sz);
            }
            function encode_integer_array(cb, args, buffer_idx) {
                var header_idx = buffer_idx;
                var intlen;
                var index;
                buffer_idx++;
                intlen = 4;
                index = 1;
                for (; ;) {
                    var sz;
                    args.value = null;
                    args.length = 4;
                    args.index = index;
                    sz = cb(args);
                    if (sz < 0) {
                        return null;
                    }
                    if (sz == 0) {
                        break;
                    }
                    if (sz == 4) {
                        var v = args.value;
                        enbuffer[buffer_idx] = v & 0xff;
                        enbuffer[buffer_idx + 1] = (v >> 8) & 0xff;
                        enbuffer[buffer_idx + 2] = (v >> 16) & 0xff;
                        enbuffer[buffer_idx + 3] = (v >> 24) & 0xff;
                    } else {
                        alert("support 32bit integer only");
                    }
                    buffer_idx += intlen;
                    index++;
                }
                if (buffer_idx == header_idx + 1) {
                    return header_idx;
                }
                enbuffer[header_idx] = intlen & 0xff;
                return buffer_idx;
            }
            function encode_array(cb, args, data_idx) {
                var buffer_idx;
                var sz;
                buffer_idx = data_idx + SIZEOF_LENGTH;
                switch (args.type) {
                    case SPROTO_TINTEGER:
                        buffer_idx = encode_integer_array(cb, args, buffer_idx);
                        if (buffer_idx == null) {
                            return -1;
                        }
                        break;
                    case SPROTO_TBOOLEAN:
                        args.index = 1;
                        for (; ;) {
                            var v = 0;
                            args.value = v;
                            args.length = 4;
                            sz = cb(args);
                            if (sz < 0) {
                                return -1;
                            }
                            if (sz == 0) {
                                break;
                            }
                            enbuffer[buffer_idx] = v ? 1 : 0;
                            buffer_idx += 1;
                            ++args.index;
                        }
                        break;
                    default:
                        args.index = 1;
                        for (; ;) {
                            args.value = buffer_idx + SIZEOF_LENGTH;
                            // args.length = size;
                            sz = cb(args);
                            if (sz == 0) {
                                break;
                            }
                            if (sz < 0) {
                                return -1;
                            }
                            if (args.type == SPROTO_TSTRING) {
                                --sz;
                            }
                            fill_size(buffer_idx, sz);
                            buffer_idx += SIZEOF_LENGTH + sz;
                            ++args.index;
                        }
                        break;
                }
                sz = buffer_idx - (data_idx + SIZEOF_LENGTH);
                if (sz == 0) {
                    return 0;
                }
                return fill_size(data_idx, sz);
            }

            args.ud = ud;
            data_idx = header_idx + header_sz;
            index = 0;
            lasttag = -1;
            for (i = 0; i < st.n; i++) {
                var f = st.f[i];
                var type = f.type;
                var value = 0;
                var sz = -1;
                args.tagname = f.name;
                args.tagid = f.tag;
                if (f.st != null) {
                    args.subtype = sproto.type[f.st];
                } else {
                    args.subtype = null;
                }
                if (type & SPROTO_TARRAY) {
                    args.type = type & ~SPROTO_TARRAY;
                    sz = encode_array(cb, args, data_idx);
                } else {
                    args.type = type;
                    args.index = 0;
                    switch (type) {
                        case SPROTO_TINTEGER:
                        case SPROTO_TBOOLEAN:
                            args.value = 0;
                            args.length = 4;
                            sz = cb(args);
                            if (sz < 0) {
                                return -1;
                            }
                            if (sz == 0) {
                                continue;
                            }
                            if (sz == 4) {
                                if (args.value < 0x7fff) {
                                    value = (args.value + 1) * 2;
                                    sz = 2;
                                } else {
                                    sz = encode_integer(args.value, data_index);
                                }
                            } else {
                                alert("support 32bits integer only");
                                return -1;
                            }
                            break;
                        case SPROTO_TSTRUCT:
                        case SPROTO_TSTRING:
                            sz = encode_object(cb, args, data_idx);
                            break;
                    }
                }
                if (sz < 0) {
                    return -1;
                }
                if (sz > 0) {
                    var record_idx, tag;
                    if (value == 0) {
                        data_idx += sz;
                    }
                    record_idx = header_idx + SIZEOF_HEADER + SIZEOF_FIELD * index;
                    tag = f.tag - lasttag - 1;
                    if (tag > 0) {
                        tag = (tag - 1) * 2 + 1;
                        if (tag > 0xffff) {
                            return -1;
                        }
                        enbuffer[record_idx] = tag & 0xff;
                        enbuffer[record_idx + 1] = (tag >> 8) & 0xff;
                        ++index;
                        record_idx += SIZEOF_FIELD;
                    }
                    ++index;
                    enbuffer[record_idx] = value & 0xff;
                    enbuffer[record_idx + 1] = (value >> 8) & 0xff;
                    lasttag = f.tag;
                }
            }
            enbuffer[header_idx] = index & 0xff;
            enbuffer[header_idx + 1] = (index >> 8) & 0xff;
            datasz = data_idx - (header_idx + header_sz);
            data_idx = header_idx + header_sz;
            if (index != st.maxn) {
                var v = enbuffer.slice(data_idx, data_idx + datasz);
                for (var s = 0; s < v.length; s++) {
                    enbuffer[header_idx + SIZEOF_HEADER + index * SIZEOF_FIELD + s] = v[s];
                }
            }
            return SIZEOF_HEADER + index * SIZEOF_FIELD + datasz;
        }
        function encode(args) {
            var self = args.ud;
            if (self.deep >= ENCODE_DEEPLEVEL) {
                alert("table is too deep");
                return -1;
            }
            if (self.indata[args.tagname] == null) {
                return 0;
            }
            if (args.index > 0) {
                if (args.tagname != self.array_tag) {
                    self.array_tag = args.tagname;
                }
                if (self.indata[args.tagname][args.index] == null) {
                    return 0;
                }
            }
            switch (args.type) {
                case SPROTO_TINTEGER:
                case SPROTO_TBOOLEAN:
                    if (args.index == 0) {
                        args.value = self.indata[args.tagname];
                    } else {
                        args.value = self.indata[args.tagname][args.index];
                    }
                    return 4;
                case SPROTO_TSTRING:
                    var str;
                    if (args.index == 0) {
                        str = self.indata[args.tagname];
                    } else {
                        str = self.indata[args.tagname][args.index];
                    }
                    for (var i = 0; i < str.length; i++) {
                        enbuffer[args.value + i] = str.charCodeAt(i);
                    }
                    return str.length + 1;
                case SPROTO_TSTRUCT:
                    var sub = new Object();
                    var r;
                    sub.st = args.subtype;
                    sub.deep = self.deep + 1;
                    if (args.index == 0) {
                        sub.indata = self.indata[args.tagname];
                    } else {
                        sub.indata = self.indata[args.tagname][args.index];
                    }
                    r = sproto_encode(args.subtype, args.value, encode, sub);
                    return r;
                default:
                    return -1;
            }
        }
        function gen_response(response, session) {
            return function (args) {
                header_tmp = {}
                header_tmp.type = null;
                header_tmp.session = session;
                var header = sproto.encode(sproto.__package, header_tmp);
                if (response) {
                    var content = sproto.encode(response, args);
                    return sproto.pack(array_concat(header, content));
                } else {
                    return sproto.pack(header);
                }
            }
        }

        sproto.encode = function (type, indata) {
            var self = new Object();
            var st = sproto_type(type);
            var tbl_index = 2;
            enbuffer = new Array();
            self.st = st;
            self.tbl_index = tbl_index;
            self.indata = indata;
            for (; ;) {
                var r;
                self.array_tag = null;
                self.array_index = 0;
                self.deep = 0;
                self.iter_index = tbl_index + 1;
                if (sproto_encode(st, 0, encode, self) < 0) {
                    return null;
                } else {
                    return { buf: enbuffer, sz: enbuffer.length };
                }
            }
        }
        function objlen(type, inbuf) {
            var ud = new Object();
            ud.array_tag = null;
            ud.deep = 0;
            ud.result = new Object();
            return sproto_decode(sproto_type(type), inbuf.buf, inbuf.sz, decode, ud);
        }
        sproto.decode = function (type, inbuf) {
            var buffer = inbuf.buf;
            var sz = inbuf.sz;
            var ud = new Object();
            ud.array_tag = null;
            ud.deep = 0;
            ud.result = new Object();
            if (sproto_decode(sproto_type(type), buffer, sz, decode, ud) == null) {
                return null;
            } else {
                return ud.result;
            }
        }
        sproto.pack = function (inbuf) {
            var tmp = new Array();
            var i, ff_srcstart, ff_desstart;
            ff_srcstart = new Array();
            var ff_srcstart_idx = 0;
            var ff_n = 0;
            var size = 0;
            var src = inbuf.buf;
            var buffer = new Array();
            var srcsz = inbuf.sz;
            var src_idx = 0;
            var buffer_idx = 0;
            var bufsz = 1 << 30;
            function write_ff(src, des_idx, nn) {
                var i;
                var align8_n = (nn + 7) & (~7);
                buffer[des_idx] = 0xff;
                buffer[des_idx + 1] = align8_n / 8 - 1;
                for (i = 0; i < nn; i++) {
                    buffer[des_idx + 2 + i] = src[i];
                }
                for (i = 0; i < align8_n - nn; i++) {
                    buffer[des_idx + nn + 2 + i] = 0;
                }
            }
            function pack_seg(s_idx, b_idx, sz, nn) {
                var header = 0;
                var notzero = 0;
                var i;
                var obuffer_idx = b_idx;
                b_idx++;
                sz--;
                if (sz < 0) {
                    obuffer_idx = null;
                }
                for (i = 0; i < 8; i++) {
                    if (src[s_idx + i] != 0) {
                        notzero++;
                        header |= 1 << i;
                        if (sz > 0) {
                            buffer[b_idx] = src[s_idx + i];
                            ++b_idx;
                            --sz;
                        }
                    }
                }
                if ((notzero == 7 || notzero == 6) && nn > 0) {
                    notzero = 8;
                }
                if (notzero == 8) {
                    if (nn > 0) {
                        return 8;
                    } else {
                        return 10;
                    }
                }
                if (obuffer_idx != null) {
                    buffer[obuffer_idx] = header;
                }
                return notzero + 1;
            }
            for (i = 0; i < srcsz; i += 8) {
                var n;
                var padding = i + 8 - srcsz;
                if (padding > 0) {
                    var j;
                    for (var k = 0; k < 8 - padding; k++) {
                        tmp[k] = src[src_idx + k];
                    }
                    for (j = 0; j < padding; j++) {
                        tmp[7 - j] = 0;
                    }
                    src = tmp;
                    src_idx = 0;
                }
                n = pack_seg(src_idx, buffer_idx, bufsz, ff_n);
                bufsz -= n;
                if (n == 10) {
                    ff_srcstart = src.slice(src_idx);
                    ff_srcstart_idx = src_idx;
                    ff_desstart = buffer_idx;
                    ff_n = 1;
                } else if (n == 8 && ff_n > 0) {
                    ++ff_n;
                    if (ff_n == 256) {
                        if (bufsz >= 0) {
                            write_ff(ff_srcstart, ff_desstart, 256 * 8);
                        }
                        ff_n = 0;
                    }
                } else {
                    if (ff_n > 0) {
                        if (bufsz >= 0) {
                            write_ff(ff_srcstart, ff_desstart, ff_n * 8);
                        }
                        ff_n = 0;
                    }
                }
                src_idx += 8;
                buffer_idx += n;
                size += n;
            }
            if (bufsz >= 0) {
                if (ff_n == 1) {
                    write_ff(ff_srcstart, ff_desstart, 8);
                } else if (ff_n > 1) {
                    write_ff(ff_srcstart, ff_desstart, srcsz - ff_srcstart_idx);
                }
            }
            return { buf: buffer, sz: size };
        }
        sproto.unpack = function (inbuf) {
            var srcv = inbuf.buf;
            var srcsz = inbuf.sz;
            var bufferv = new Array();
            var bufsz = 1 << 30;
            var src = srcv;
            var src_idx = 0;
            var buffer = bufferv;
            var buffer_idx = 0;
            var size = 0;
            while (srcsz > 0) {
                var header = src[src_idx];
                --srcsz;
                ++src_idx
                if (header == 0xff) {
                    var n;
                    if (srcsz < 0) {
                        return null;
                    }
                    n = (src[src_idx] + 1) * 8;
                    if (srcsz < n + 1) {
                        return null;
                    }
                    srcsz -= n + 1;
                    src_idx++
                    if (bufsz >= n) {
                        for (var i = 0; i < n; i++) {
                            buffer[buffer_idx + i] = src[src_idx + i];
                        }
                    }
                    bufsz -= n;
                    buffer_idx += n;
                    src_idx += n;
                    size += n;
                } else {
                    var i;
                    for (i = 0; i < 8; i++) {
                        var nz = (header >>> i) & 1;
                        if (nz != 0) {
                            if (srcsz < 0) {
                                return null;
                            }
                            if (bufsz > 0) {
                                buffer[buffer_idx] = src[src_idx];
                                --bufsz;
                                ++buffer_idx;
                            }
                            ++src_idx;
                            --srcsz;
                        } else {
                            if (bufsz > 0) {
                                buffer[buffer_idx] = 0;
                                --bufsz;
                                ++buffer_idx;
                            }
                        }
                        ++size;
                    }
                }
            }
            return { buf: buffer, sz: size }
        }

        sproto.protocol = sproto_protoquery;
        sproto.pencode = function (type, buf) {
            var o = sproto.encode(type, buf);
            if (o == null) {
                return null;
            }
            return sproto.pack(o);
        }
        sproto.pdecode = function (type, buf) {
            var o = sproto.unpack(buf);
            if (o == null) {
                return null;
            }
            return sproto.decode(type, o);
        }
        sproto.host = function (packagename) {
            sproto.__package = packagename;
            sproto.__session = new Array();
        }
        sproto.attach = function () {
            return function (name, args, session) {
                var proto = sproto_protoquery_name(name);
                var header_tmp = {};
                header_tmp.type = proto.tag;
                header_tmp.session = session;
                var header = sproto.encode(sproto.__package, header_tmp);
                if (session) {
                    sproto.__session[session] = proto.p[SPROTO_RESPONSE] ? proto.p[SPROTO_RESPONSE] : true;
                }
                if (args) {
                    var content = sproto.encode(proto.p[SPROTO_REQUEST].name, args);
                    return sproto.pack(array_concat(header, content));
                } else {
                    return sproto.pack(header);
                }
            }
        }
        sproto.dispatch = function (buf, req_cb, rsp_cb) {
            var bin = sproto.unpack(buf);
            var header = sproto.decode(sproto.__package, bin);
            var len = objlen(sproto.__package, bin);
            var content = bin.buf.slice(len);
            if (header.type) {
                var proto = sproto.protocol(header.type, SPROTO_REQUEST);
                var result;
                if (proto.p[SPROTO_REQUEST]) {
                    result = sproto.decode(proto.p[SPROTO_REQUEST], { buf: content, sz: content.length });
                }
                if (header.session) {
                    return req_cb(proto.name, result, gen_response(proto.p[SPROTO_RESPONSE], header.session), header.session);
                } else {
                    return req_cb(proto.name, result, null, null);
                }
            } else {
                if (!header.session) {
                    alert("session not found");
                }
                session = header.session;
                if (!sproto.__session[session]) {
                    alert("session not found");
                }
                response = sproto.__session[session];
                sproto.__session[session] = null;
                if (response == true) {
                    return rsp_cb(null, session, null);
                } else {
                    var result = sproto.decode(response.name, { buf: content, sz: content.length });
                    return rsp_cb(response.name, session, result);
                }
            }
        }

        return create_from_bundle(binsch.buf, binsch.sz);
    }
}

function array2arraybuffer(array) {
    var b = new ArrayBuffer(array.length);
    var v = new DataView(b, 0);
    for (var i = 0; i < array.length; i++) {
        v.setUint8(i, array[i]);
    }
    return b;
}

function arraybuffer2array(buffer) {
    var v = new DataView(buffer, 0);
    var a = new Array();
    for (var i = 0; i < v.byteLength; i++) {
        a[i] = v.getUint8(i);
    }
    return a;
}

