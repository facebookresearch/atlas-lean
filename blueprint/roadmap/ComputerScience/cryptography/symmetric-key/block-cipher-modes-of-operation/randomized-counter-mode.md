# Randomized counter (CTR) mode

For a PRF $F : K \times \{0,1\}^b \to \{0,1\}^b$, *randomized counter mode* encrypts $m_1 \| \cdots \| m_\ell$ by choosing a uniform $x \in \{0,1\}^b$ and outputting $x \,\|\, (m_1 \oplus F(k, x)) \| \cdots \| (m_\ell \oplus F(k, x + \ell - 1 \bmod 2^b))$.

## Depends on

- [PRF advantage](../pseudorandom-functions/prf-advantage.md)
- [Private-key encryption scheme](../../security-games/generic-security-games/symm-enc-scheme.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare, A. Desai, E. Jokipii and P. Rogaway, "A Concrete Security Treatment of Symmetric Encryption", Proceedings of the 38th Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1997.
