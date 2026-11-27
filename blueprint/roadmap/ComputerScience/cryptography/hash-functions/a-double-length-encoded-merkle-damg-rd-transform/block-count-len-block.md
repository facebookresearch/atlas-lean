# Block-count length block

Write $\langle c \rangle_w$ for the $w$-bit little-endian encoding of $c \in \mathbb{N}$: its $i$-th bit ($0 \le i < w$) is $\lfloor c / 2^i \rfloor \bmod 2$, so only the low $w$ bits of $c$ are kept and decoding returns $c \bmod 2^w$.

The block-count length block of width $n$ sends a count $c \in \mathbb{N}$ to the $n$-bit block $\langle c \rangle_n$. It keeps only the low $n$ bits of $c$, so it separates counts only below $2^n$ ([block-count blocks are injective below $2^n$](block-count-len-block-inj-on.md)); counts that agree modulo $2^n$ get the same block.

Used as the length block of the [full hash](full-hash.md), it is the second length encoding, after the bit length inside the padding. Katz and Lindell's Construction 5.3 has no block-count block.
