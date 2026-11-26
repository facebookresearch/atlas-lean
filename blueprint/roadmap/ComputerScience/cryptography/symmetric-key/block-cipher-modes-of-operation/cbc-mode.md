# CBC mode with a random initial value

For a block cipher $E$ with block length $b$, *randomized CBC* encrypts $m_1 \| \cdots \| m_\ell$ by choosing a uniform $c_0 \in \{0,1\}^b$ and setting $c_j = E(k, c_{j-1} \oplus m_j)$; the ciphertext is $c_0 \| c_1 \| \cdots \| c_\ell$. Decryption computes $m_j = D(k, c_j) \oplus c_{j-1}$.

## Depends on

- [Block cipher (uniform family)](../block-ciphers-and-strong-prps/block-cipher.md)
- [Private-key encryption scheme](../../security-games/generic-security-games/symm-enc-scheme.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare, A. Desai, E. Jokipii and P. Rogaway, "A Concrete Security Treatment of Symmetric Encryption", Proceedings of the 38th Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1997.
