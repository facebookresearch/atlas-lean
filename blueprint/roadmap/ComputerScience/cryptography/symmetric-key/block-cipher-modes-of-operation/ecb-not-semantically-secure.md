# ECB on multi-block messages is not semantically secure

For every block cipher (even a secure PRP) with block length $b \ge 1$ and messages of up to $\ell \ge 2$ blocks, the adversary submitting $m_0 = 0^b \| 0^b$ and $m_1 = 0^b \| 1^b$ and outputting $0$ iff the two ciphertext blocks are equal has one-time semantic-security advantage exactly $1$.

## Proof sketch

ECB encrypts equal blocks to equal blocks and, by injectivity of $E(k,\cdot)$, distinct blocks to distinct blocks.

## Depends on

- [Electronic codebook (ECB) mode](ecb-mode.md)
- [Semantic security with error $\varepsilon$](../../security-games/semantic-security-and-indistinguishability/semantically-secure.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
