// Port of the verified santa_reference_decoder.py.
// Original-client header restoration + Santa-reference body reconstruction.
// Does not claim to restore the original Themida metadata/registry VM.
using System;
using System.Buffers.Binary;
using System.IO;
using System.IO.Hashing;
using System.Security.Cryptography;

namespace GRF.Core
{
    internal static class GravityResourceDecryptor
    {
        private static readonly byte[] HeaderKey = Hex("56fd7e712f6d36f55ca599e67b18107a");
        private static readonly byte[] HeaderIv = Hex("4ce8a1ae45b321607e4f26a4bb140c96");
        private static readonly byte[][] ModeKeys = { Array.Empty<byte>(), Hex("8603383ec74920038a9e630407577e0b"), Hex("743e81f9bc8a066e76b6054f11c1a301"), Hex("1302fe059ce0ec6f59ec7ed3493b3d93") };
        private static readonly byte[][] ModeIvs = { Array.Empty<byte>(), Hex("b6d4a37151cdaf6847786dd3e404032f"), Hex("2c0550bd4c606759c3dc9eb256b1455b"), Hex("b180defae67c0a11f554ce7615bfe6c4") };

        /// <summary>Returns decrypted AND decompressed resource bytes.</summary>
        /// <param name="encryptedData">Exact stored entry bytes, including its 104-byte prefix.</param>
        /// <param name="filePathBytes">Original full archive-relative path bytes; do not normalize or append NUL.</param>
        /// <param name="expectedDecompressedSize">The entry's expected final size (SizeDecompressed).</param>
        /// <exception cref="ArgumentException">An argument is invalid.</exception>
        /// <exception cref="InvalidDataException">Format, size, checksum or final hash validation fails.</exception>
        public static byte[] DecryptResource(byte[] encryptedData, byte[] filePathBytes, int expectedDecompressedSize)
        {
            if (encryptedData == null) throw new ArgumentNullException(nameof(encryptedData));
            if (filePathBytes == null) throw new ArgumentNullException(nameof(filePathBytes));
            if (expectedDecompressedSize < 0)
                throw new ArgumentOutOfRangeException(nameof(expectedDecompressedSize));
            var h = DecodeHeader(encryptedData, filePathBytes);
            if (U32(h, 4) != (uint)(encryptedData.Length - 104))
                throw Bad("Stored body length does not match the header.");
            if (U32(h, 12) != (uint)expectedDecompressedSize)
                throw Bad("Expected decompressed size does not match the header.");
            uint mode = U32(h, 32);
            if (mode > 4) throw Bad("Unsupported body mode.");
            uint compression = (U32(h, 0) >> 16) & 255;
            if (compression != 0 && compression != 2)
                throw Bad("Unsupported compression selector.");
            byte[] body = Slice(encryptedData, 104, encryptedData.Length - 104);
            byte[] pathHash = Hash128(filePathBytes);
            byte[] output;
            if (mode == 0)
            {
                output = DecodeBody0(body, pathHash, h, expectedDecompressedSize);
                if (output == null && filePathBytes.Length <= 240 && encryptedData.Length >= 232)
                    output = TryFinish(FallbackBody0(body, filePathBytes, h), h, expectedDecompressedSize);
            }
            else
            {
                // Santa first accepts a body that is already the complete verified plaintext.
                if (body.Length == expectedDecompressedSize && HashMatches(body, h)) return body;
                byte[] transformed = mode == 4
                    ? TransformBody4(body, pathHash, h)
                    : TransformBody123(body, pathHash, h, (int)mode);
                output = TryFinish(transformed, h, expectedDecompressedSize);
            }
            return output ?? throw Bad("Resource decryption/decompression or final hash validation failed.");
        }

        private static byte[] DecodeHeader(byte[] raw, byte[] path)
        {
            if (raw.Length < 104 || raw[0] != 1) throw Bad("Unsupported or truncated prefix.");
            byte[] h;
            switch (raw[1])
            {
                case 1: h = AesCbc(raw, 8, 96, HeaderKey, HeaderIv); break;
                case 2: h = AesCbc(raw, 8, 96, HeaderKey, Hash128(path)); break;
                case 15: h = AesCbc(raw, 8, 96, HeaderKey, Hash128(Slice(raw, 4, 4))); break;
                case 0x71: h = DecodeHeader71(raw); break;
                default: throw Bad("Unsupported header kind.");
            }
            if (XxHash32.HashToUInt32(h) != U32(raw, 4)) throw Bad("Header checksum mismatch.");
            return h;
        }

        private static byte[] DecodeHeader71(byte[] raw)
        {
            byte[] previous = Hex("a095dfcfd04b74db027ede09"), output = new byte[96];
            for (int pos = 0; pos < 96; pos += 12)
            {
                byte[] current = Slice(raw, 8 + pos, 12);
                byte[] stream = TransformHeaderBlock(previous);
                for (int j = 0; j < 12; j++) output[pos + j] = (byte)(current[j] ^ stream[j]);
                previous = current;
            }
            return output;
        }

        private static byte[] TransformHeaderBlock(byte[] block)
        {
            unchecked
            {
                uint a = Be32(block, 0), b = Be32(block, 4), c = Be32(block, 8), rc = 0x0b0b;
                for (int i = 0; i < 11; i++)
                {
                    a ^= 0xad61aeda ^ (rc << 16); b ^= 0xbf203e1d; c ^= 0xfe1db72b ^ rc;
                    Theta(ref a, ref b, ref c);
                    uint x = Rol(a, 22), y = b, z = Rol(c, 1);
                    a = Rol((~z | y) ^ x, 1);
                    b = y ^ (~x | z);
                    c = Rol((~y | x) ^ z, 22);
                    rc <<= 1;
                    if ((rc & 0x10000) != 0) rc ^= 0x11011;
                }
                a ^= 0xad61aeda ^ (rc << 16); b ^= 0xbf203e1d; c ^= 0xfe1db72b ^ rc;
                Theta(ref a, ref b, ref c);
                byte[] r = new byte[12]; PutBe(r, 0, a); PutBe(r, 4, b); PutBe(r, 8, c); return r;
            }
        }

        private static void Theta(ref uint a, ref uint b, ref uint c)
        {
            unchecked
            {
                uint d = Rol(a ^ b ^ c, 16) ^ Rol(a ^ b ^ c, 8);
                uint e = (((a >> 16) ^ c) >> 8) ^ (((a << 16) ^ b) << 8);
                uint f = (((b << 16) ^ c) << 8) ^ (((b >> 16) ^ a) >> 8);
                a ^= e ^ d; b ^= f ^ d; c ^= (f << 16) ^ (e >> 16) ^ d;
            }
        }

        private static byte[] TransformBody123(byte[] body, byte[] pathHash, byte[] h, int mode)
        {
            byte[] output = (byte[])body.Clone(), key = ModeKeys[mode];
            byte[] stream = DeriveStream(pathHash, Slice(h, 16, 16), Slice(key, 5, 8));
            int rest = Math.Max(0, body.Length - 128);
            if (rest >= 0xc00)
            {
                byte[] p = AesCbc(body, 128 + 0x800, 0x400, key, ModeIvs[mode]);
                Buffer.BlockCopy(p, 0, output, 128 + 0x800, p.Length);
            }
            else
            {
                int n = rest / 16 * 16;
                if (n != 0)
                {
                    byte[] p = AesCbc(body, 128, n, key, ModeIvs[mode]);
                    Buffer.BlockCopy(p, 0, output, 128, p.Length);
                }
            }
            XorRepeat(output, 128, stream);
            return output;
        }

        private static byte[] TransformBody4(byte[] body, byte[] pathHash, byte[] h)
        {
            byte[] seed = new byte[16], mixConstant = Hex("0d3c05210e3f082a5c2f49a0910bb54c");
            byte[] seedConstant = Hex("64db6b81ddbf54e14b077c728bad590a");
            for (int i = 0; i < 16; i++)
                seed[i] = (byte)(h[i < 8 ? 24 + i : 8 + i] ^ seedConstant[i]);
            byte[] mixed = new byte[16];
            for (int i = 0; i < 16; i++) mixed[i] = (byte)(seed[i] ^ mixConstant[i]);
            byte[] seed8 = new byte[8];
            Buffer.BlockCopy(mixed, 9, seed8, 0, 7); seed8[7] = (byte)(mixed[0] ^ 0x94);
            byte[] stream = DeriveStream(Slice(h, 16, 16), pathHash, seed8);
            byte[] output = (byte[])body.Clone(), previous = mixed;
            uint[] schedule = Rc6Schedule(seed);
            int n = Math.Min(Math.Max(0, body.Length - 128), 0x400) / 16 * 16;
            for (int pos = 128; pos < 128 + n; pos += 16)
            {
                byte[] current = Slice(body, pos, 16), mask = Rc6Encrypt(previous, schedule);
                for (int i = 0; i < 16; i++) output[pos + i] = (byte)(current[i] ^ mask[i]);
                previous = current;
            }
            XorRepeat(output, 128, stream);
            return output;
        }

        private static byte[] DecodeBody0(byte[] body, byte[] pathHash, byte[] h, int size)
        {
            for (int choice = 0; choice < 2; choice++)
            {
                byte[] key = Slice(h, choice == 0 ? 64 : 36, 16);
                byte[] iv = Slice(h, choice == 0 ? 80 : 52, 16);
                byte[] stream = choice == 0
                    ? DeriveStream(pathHash, Slice(h, 16, 16), Slice(h, 88, 8))
                    : DeriveStream(Slice(h, 16, 16), pathHash, Slice(h, 84, 8));
                for (int budget = 0x410; budget <= 0x2490; budget += 0x410)
                {
                    using var candidate = new MemoryStream(body.Length);
                    candidate.Write(body, 0, Math.Min(body.Length, 128));
                    int pos = 128, left = budget;
                    while (left >= 16 && pos < body.Length)
                    {
                        int n = Math.Min(Math.Min((body.Length - pos) / 16 * 16, left), 0x410);
                        if (n < 16) break;
                        byte[] block = AesCbc(body, pos, n, key, iv);
                        candidate.Write(block, 0, n >= 32 ? n - 16 : n);
                        pos += n; left -= n;
                    }
                    // Python slicing past the end of a short body yields an empty tail.
                    int tailStart = Math.Min(pos, body.Length);
                    byte[] tail = Slice(body, tailStart, body.Length - tailStart);
                    XorRepeat(tail, 0, stream); candidate.Write(tail, 0, tail.Length);
                    byte[] result = TryFinish(candidate.ToArray(), h, size);
                    if (result != null) return result;
                }
                int aligned = Math.Max(0, body.Length - 128) / 16 * 16;
                if (aligned != 0)
                {
                    byte[] candidate = (byte[])body.Clone();
                    byte[] plain = AesCbc(body, 128, aligned, key, iv);
                    Buffer.BlockCopy(plain, 0, candidate, 128, aligned);
                    byte[] result = TryFinish(candidate, h, size);
                    if (result != null) return result;
                }
            }
            return TryFinish(body, h, size);
        }

        private static byte[] FallbackBody0(byte[] body, byte[] path, byte[] h)
        {
            byte[] h1 = Hash128(path, U32(h, 12));
            byte[] h2 = Hash128(Slice(h, 36, 60), U64(h1, 8));
            uint[] words = new uint[4], keys = new uint[8];
            int[] map = { 5, 4, 7, 6 };
            for (int i = 0; i < 4; i++)
            {
                uint w = words[i] = Be32(h2, i * 4);
                keys[i] = w ^ Rol(w, 1) ^ Rol(w, 8);
                keys[map[i]] = w ^ Rol(w, 1) ^ Rol(w, 11);
            }
            byte[] output = (byte[])body.Clone(), previous = Slice(h, 16, 16);
            int aligned = (body.Length - 128) / 16 * 16;
            for (int pos = 128; pos < 128 + Math.Min(aligned, 1024); pos += 16)
            {
                byte[] current = Slice(output, pos, 16), plain = FallbackBlock(current, keys);
                for (int i = 0; i < 16; i++) output[pos + i] = (byte)(plain[i] ^ previous[i]);
                previous = current;
            }
            previous = Slice(h, 16, 16);
            for (int pos = 128; pos < 128 + aligned; pos += 16)
            {
                byte[] current = Slice(output, pos, 16);
                for (int i = 0; i < 16; i++)
                {
                    int j = (i + 12) & 15;
                    output[pos + i] = (byte)(previous[i] ^ current[j] ^ h1[j]);
                }
                previous = current;
            }
            for (int i = 0; i < body.Length - 128 - aligned; i++)
                output[128 + aligned + i] ^= (byte)(previous[i] ^ h1[i]);
            return output;
        }

        private static byte[] FallbackBlock(byte[] block, uint[] keys)
        {
            unchecked
            {
                uint[] w = { Be32(block, 0), Be32(block, 4), Be32(block, 8), Be32(block, 12) };
                for (int r = 79; r >= 0; r--)
                {
                    uint part = Rol(w[(r + 1) & 3], (r & 1) != 0 ? 8 : 1) ^ keys[r & 7];
                    w[r & 3] = (Rol(w[r & 3], (r & 1) != 0 ? 31 : 24) - part) ^ (uint)r;
                }
                byte[] output = new byte[16];
                for (int i = 0; i < 4; i++) PutBe(output, i * 4, w[i]);
                return output;
            }
        }

        private static byte[] DeriveStream(byte[] first, byte[] key, byte[] seed8)
        {
            uint[] k = new uint[52];
            for (int i = 0; i < 8; i++) k[i] = BinaryPrimitives.ReadUInt16BigEndian(key.AsSpan(i * 2, 2));
            for (int i = 8; i < 52; i++)
            {
                int b = i & ~7;
                k[i] = ((k[b + ((i + 1) & 7) - 8] << 9) | (k[b + ((i + 2) & 7) - 8] >> 7)) & 65535;
            }
            byte[] block = new byte[8];
            for (int i = 0; i < 8; i++) block[i] = (byte)(first[i] ^ seed8[i]);
            byte[] left = IdeaEncrypt(block, k);
            for (int i = 0; i < 8; i++) block[i] = (byte)(first[i + 8] ^ left[i]);
            byte[] right = IdeaEncrypt(block, k), output = new byte[16];
            Buffer.BlockCopy(left, 0, output, 0, 8); Buffer.BlockCopy(right, 0, output, 8, 8);
            return output;
        }

        private static uint IdeaMul(uint a, uint b) => (uint)(((ulong)(a == 0 ? 65536 : a) * (b == 0 ? 65536u : b) % 65537) & 65535);

        private static byte[] IdeaEncrypt(byte[] block, uint[] k)
        {
            uint a = BinaryPrimitives.ReadUInt16BigEndian(block.AsSpan(0, 2));
            uint b = BinaryPrimitives.ReadUInt16BigEndian(block.AsSpan(2, 2));
            uint c = BinaryPrimitives.ReadUInt16BigEndian(block.AsSpan(4, 2));
            uint d = BinaryPrimitives.ReadUInt16BigEndian(block.AsSpan(6, 2));
            for (int r = 0; r < 8; r++)
            {
                int j = r * 6;
                a = IdeaMul(a, k[j]); b = (b + k[j + 1]) & 65535;
                c = (c + k[j + 2]) & 65535; d = IdeaMul(d, k[j + 3]);
                uint e = IdeaMul(a ^ c, k[j + 4]);
                uint f = IdeaMul(((b ^ d) + e) & 65535, k[j + 5]);
                e = (e + f) & 65535;
                (a, b, c, d) = (a ^ f, c ^ f, b ^ e, d ^ e);
            }
            byte[] output = new byte[8];
            uint[] result = { IdeaMul(a, k[48]), (c + k[49]) & 65535,
            (b + k[50]) & 65535, IdeaMul(d, k[51]) };
            for (int i = 0; i < 4; i++)
                BinaryPrimitives.WriteUInt16BigEndian(output.AsSpan(i * 2, 2), (ushort)result[i]);
            return output;
        }

        private static uint[] Rc6Schedule(byte[] key)
        {
            unchecked
            {
                uint[] words = { U32(key, 0), U32(key, 4), U32(key, 8), U32(key, 12) };
                uint[] s = new uint[44];
                for (int i = 0; i < 44; i++) s[i] = 0xb7e15163 + (uint)i * 0x9e3779b9;
                uint a = 0, b = 0; int x = 0, y = 0;
                for (int i = 0; i < 132; i++)
                {
                    a = s[x] = Rol(s[x] + a + b, 3);
                    b = words[y] = Rol(words[y] + a + b, (int)((a + b) & 31));
                    x = (x + 1) % 44; y = (y + 1) % 4;
                }
                return s;
            }
        }

        private static byte[] Rc6Encrypt(byte[] block, uint[] s)
        {
            unchecked
            {
                uint a = U32(block, 0), b = U32(block, 4) + s[0], c = U32(block, 8), d = U32(block, 12) + s[1];
                for (int i = 1; i <= 20; i++)
                {
                    uint t = Rol(b * (2 * b + 1), 5), u = Rol(d * (2 * d + 1), 5);
                    a = Rol(a ^ t, (int)(u & 31)) + s[2 * i];
                    c = Rol(c ^ u, (int)(t & 31)) + s[2 * i + 1];
                    (a, b, c, d) = (b, c, d, a);
                }
                byte[] r = new byte[16]; PutLe(r, 0, a + s[42]); PutLe(r, 4, b);
                PutLe(r, 8, c + s[43]); PutLe(r, 12, d); return r;
            }
        }

        private static byte[] TryFinish(byte[] candidate, byte[] h, int size)
        {
            if (candidate.Length == size && HashMatches(candidate, h)) return candidate;
            byte[] output;
            try { output = DecodeLz4Partial(candidate, size); }
            catch (InvalidDataException) { return null; }
            return HashMatches(output, h) ? output : null;
        }

        // The reference decoder stops at the expected output size, allowing stored padding.
        // Partial output is never returned unless its final XXH3-128 hash also matches.
        private static byte[] DecodeLz4Partial(byte[] data, int size)
        {
            byte[] output = new byte[size]; int pos = 0, written = 0;
            while (pos < data.Length && written < size)
            {
                int token = data[pos++];
                int literal = ReadLength(data, ref pos, token >> 4);
                int take = Math.Min(literal, size - written);
                if (take > data.Length - pos) throw Bad("Truncated LZ4 literal.");
                Buffer.BlockCopy(data, pos, output, written, take); written += take;
                if (written == size) break;
                if (literal > data.Length - pos) throw Bad("Truncated LZ4 literal.");
                pos += literal;
                if (pos > data.Length - 2) throw Bad("Truncated LZ4 match.");
                int distance = data[pos] | (data[pos + 1] << 8); pos += 2;
                if (distance == 0 || distance > written) throw Bad("Invalid LZ4 match offset.");
                int encoded = ReadLength(data, ref pos, token & 15);
                if (encoded > int.MaxValue - 4) throw Bad("LZ4 length overflow.");
                int match = Math.Min(encoded + 4, size - written);
                for (int i = 0; i < match; i++) output[written + i] = output[written + i - distance];
                written += match;
            }
            if (written != size) throw Bad("Wrong decompressed size.");
            return output;
        }

        private static int ReadLength(byte[] data, ref int pos, int length)
        {
            if (length != 15) return length;
            while (true)
            {
                if (pos >= data.Length) throw Bad("Truncated LZ4 length.");
                int b = data[pos++];
                if (length > int.MaxValue - b) throw Bad("LZ4 length overflow.");
                length += b; if (b != 255) return length;
            }
        }

        private static byte[] AesCbc(byte[] source, int offset, int count, byte[] key, byte[] iv)
        {
            using Aes aes = Aes.Create();
            aes.Mode = CipherMode.CBC; aes.Padding = PaddingMode.None; aes.Key = key; aes.IV = iv;
            using ICryptoTransform decryptor = aes.CreateDecryptor();
            return decryptor.TransformFinalBlock(source, offset, count);
        }

        private static byte[] Hash128(byte[] input, ulong seed = 0)
        {
            // .NET returns the canonical big-endian digest. The client stores low64 then high64.
            byte[] bytes = XxHash128.Hash(input, unchecked((long)seed));
            Array.Reverse(bytes); return bytes;
        }
        private static bool HashMatches(byte[] output, byte[] header) => Hash128(output).AsSpan().SequenceEqual(header.AsSpan(16, 16));
        private static void XorRepeat(byte[] data, int start, byte[] mask)
        {
            for (int i = start; i < data.Length; i++) data[i] ^= mask[(i - start) & 15];
        }
        private static uint Rol(uint x, int n) { n &= 31; return (x << n) | (x >> ((32 - n) & 31)); }
        private static uint U32(byte[] b, int o) => BinaryPrimitives.ReadUInt32LittleEndian(b.AsSpan(o, 4));
        private static ulong U64(byte[] b, int o) => BinaryPrimitives.ReadUInt64LittleEndian(b.AsSpan(o, 8));
        private static uint Be32(byte[] b, int o) => BinaryPrimitives.ReadUInt32BigEndian(b.AsSpan(o, 4));
        private static void PutBe(byte[] b, int o, uint v) => BinaryPrimitives.WriteUInt32BigEndian(b.AsSpan(o, 4), v);
        private static void PutLe(byte[] b, int o, uint v) => BinaryPrimitives.WriteUInt32LittleEndian(b.AsSpan(o, 4), v);
        private static byte[] Slice(byte[] source, int offset, int count) => source.AsSpan(offset, count).ToArray();
        private static byte[] Hex(string s)
        {
            byte[] bytes = new byte[s.Length / 2];
            for (int i = 0; i < bytes.Length; i++) bytes[i] = Convert.ToByte(s.Substring(i * 2, 2), 16);
            return bytes;
        }
        private static InvalidDataException Bad(string message) => new(message);
    }
}
