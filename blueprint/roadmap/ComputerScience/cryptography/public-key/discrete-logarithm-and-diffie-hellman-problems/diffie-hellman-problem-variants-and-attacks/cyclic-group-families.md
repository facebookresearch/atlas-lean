# Cyclic and prime-order group families

A *cyclic group family* consists of a polynomial-time sampler of group descriptions $d$ at security parameter $n$, together with polynomial-time algorithms for the group operation, inversion, equality and encoding of elements as bit strings in a cyclic group $G_d$ of order $q_d$ with a distinguished generator $g_d$. A *prime-order* family has $q_d$ prime; it is *decodable* if membership of a bit string in the encoding of $G_d$ is decidable in polynomial time. Exponents are drawn from $\mathbb{Z}_{q_d}$, and the DL, CDH and DDH experiments are run relative to the setup law of $d$.

## Depends on

- [Group exponentiation with modular exponents](../../diffie-hellman-key-exchange/gpow.md)
- [Discrete-logarithm experiment](../../hardness-assumptions/dlog-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
