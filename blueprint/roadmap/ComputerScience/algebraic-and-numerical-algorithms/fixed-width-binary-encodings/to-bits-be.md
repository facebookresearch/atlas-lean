# Fixed-width big-endian encoding of a natural number

The $w$-bit big-endian encoding of a natural number $n$ is the bit string of length $w$ whose entry $i$ is
bit $w - 1 - i$ of $n$, for $0 \le i < w$. Only the low $w$ bits of $n$ are kept. It serializes integers
as fixed-length strings, for example in padded RSA and RSA-OAEP (Katz and Lindell, 2nd ed., Section 11.5).
