# CBC-MAC

For a PRF $F : K \times \{0,1\}^n \to \{0,1\}^n$, the (raw, zero-IV) *CBC-MAC* of a message of whole blocks $m_1 \| \cdots \| m_\ell$ is $t_\ell$, where $t_0 = 0^n$ and $t_j = F(k, t_{j-1} \oplus m_j)$. The *length-prepended* variant evaluates CBC-MAC on $\langle \ell \rangle \| m_1 \| \cdots \| m_\ell$, where $\langle \ell\rangle$ is an $n$-bit encoding of the block count.

## Depends on

- [PRF advantage](../pseudorandom-functions/prf-advantage.md)
- [Message authentication code](../../security-games/generic-security-games/macscheme.md)

## Sources

- M. Bellare, J. Kilian and P. Rogaway, "The Security of the Cipher Block Chaining Message Authentication Code", Journal of Computer and System Sciences 61(3), 2000.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
