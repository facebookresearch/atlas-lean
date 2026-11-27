# Electronic codebook (ECB) mode

For a block cipher $E$ with block length $b$, ECB encrypts a message $m = m_1 \| \cdots \| m_\ell$ of whole blocks under key $k$ as $E(k, m_1) \| \cdots \| E(k, m_\ell)$ and decrypts blockwise with $D$. It is deterministic and stateless.

## Depends on

- [Block cipher (uniform family)](../block-ciphers-and-strong-prps/block-cipher.md)
- [Private-key encryption scheme](../../security-games/generic-security-games/symm-enc-scheme.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
