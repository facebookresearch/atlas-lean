# Binary encoding of natural numbers

The bitstring encoding of $\mathbb{N}$ that writes
$0$ as the empty string and a positive integer $n$ as its binary digits, least significant bit
first, together with Mathlib's decoding map, which recovers $n$ from its encoding. It is a
definition, not an instance; Theorem 3 installs it locally so that lists of piles are encoded as
self-delimiting binary blocks.

## Sources

- Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1, Theorem 3 ("integers are presented in binary").
