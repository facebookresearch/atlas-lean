# Full-domain-hash signatures

Let $T$ be a one-way trapdoor permutation on a set $X$ and $H$ a hash function onto $X$ modelled as a random oracle. In the full-domain-hash signature scheme, the signature of $m$ is $\sigma = T^{-1}(sk, H(m))$ and verification checks $T(pk, \sigma) = H(m)$. The scheme is existentially unforgeable under chosen-message attacks: for every forger $A$ making at most $Q_{\mathrm{ro}}$ random-oracle queries and $Q_s$ signing queries there is an inverter $B$ with

$$\mathrm{Adv}^{\mathrm{SIG}}[A] \le (Q_{\mathrm{ro}} + Q_s + 1)\cdot \mathrm{Adv}^{\mathrm{OW}}[B, T],$$


obtained by programming $H$ at a guessed query. RSA-FDH is secure under the RSA assumption.

## Depends on

- [Trapdoor permutations](../hardness-assumptions/trapdoor-permutations.md)
- [The random oracle model](the-random-oracle-model.md)
- [Polynomial-query unforgeability of signatures](../../security-games/asymptotic-security/poly-query-sig-secure.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorem 13.3
- M. Bellare and P. Rogaway, "The exact security of digital signatures: how to sign with RSA and Rabin", *EUROCRYPT 1996*, LNCS 1070, Springer, 1996
