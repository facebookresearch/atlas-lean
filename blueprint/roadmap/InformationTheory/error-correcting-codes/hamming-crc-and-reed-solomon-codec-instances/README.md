# Hamming, CRC and Reed-Solomon codec instances

- [Hamming(7,4) codec](encoding.md)
- [Hamming(7,4) codewords have length seven](encoding-encode-length.md)
- [Hamming(7,4) codec on a seven-bit word](encoding-decode-of-fn.md)
- [CRC codec](encoding-2.md)
- [Reed–Solomon codec](encoding-3.md)
- [Reed–Solomon codewords have length n](encoding-encode-length-2.md)

The detection and correction guarantees of these codecs are stated with their codes: for CRC, the [detection criterion](../cyclic-redundancy-checks/dvd-encode-add-iff.md), [detection of single-symbol errors](../cyclic-redundancy-checks/not-dvd-c-mul-x-pow.md) and [detection of short bursts](../cyclic-redundancy-checks/not-dvd-of-is-burst-le.md); for Reed–Solomon, [correction of up to $\lfloor (n-k)/2 \rfloor$ errors](../reed-solomon-codes/decode-encode-add.md) and [when decoding fails](../reed-solomon-codes/decode-eq-none-iff.md). The Hamming one-error result is linked from the [seven-bit word page](encoding-decode-of-fn.md).
