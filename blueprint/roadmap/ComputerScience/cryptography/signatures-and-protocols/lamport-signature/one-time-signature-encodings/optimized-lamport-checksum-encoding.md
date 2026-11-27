# The optimized Lamport checksum encoding is containment free

For $v$-bit messages and $w$ with $v < 2^{w}$, let $P_{\mathrm{opt}}(m)$ be the set of positions of the $1$ bits of $m$ together with the positions of the $1$ bits of a $w$-bit encoding of the number of $0$ bits of $m$. Then $P_{\mathrm{opt}}$ is containment free; with $v$ a power of two and $w = \log_2 v + 1$ this gives Lamport signatures with $v + w$ rather than $2v$ public-key blocks.

## Proof sketch

If $P(m) \subseteq P(m')$ with $m \ne m'$, the ones of $m$ are among the ones of $m'$, so $m'$ has strictly fewer zeros; but then the checksum of $m'$ is numerically smaller and its one-positions cannot contain those of $m$'s checksum, a contradiction.

## Depends on

- [Containment-free and domination-free encodings](containment-and-domination-free-encodings.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- R. C. Merkle, "A Certified Digital Signature", Advances in Cryptology (CRYPTO 1989), LNCS 435, 1990.
