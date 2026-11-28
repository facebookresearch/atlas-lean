# Length field encoding

The $w$-bit little-endian encoding of a natural number $n$ lists the binary digits of $n$ from the
least significant upward, keeping the $w$ lowest ones. It is the length field of Katz and Lindell,
Construction 5.3, with a configurable width.

The $n$-bit block that the [double-length-encoded full hash](../a-double-length-encoded-merkle-damg-rd-transform/full-hash.md) appends sends a block count $c$ to this encoding with $w = n$, packaged as a block of length $n$. It keeps only the low $n$ bits of $c$, so counts that agree modulo $2^n$ get the same block; it is the second length encoding there, after the bit length inside the padding. Katz and Lindell's Construction 5.3 has no block-count block.
