# Full-domain-hash signatures

Let $T$ be a one-way trapdoor permutation on a finite set $X$. At each security and system parameter $(\lambda,\Lambda)$, $X$ is fixed **before** key generation and does not depend on the generated public key (Definition 10.4). Let $H$ be a hash function with codomain $X$ modelled as a random oracle. In the full-domain-hash signature scheme, the signature of $m$ is $\sigma = T^{-1}(sk, H(m))$ and verification checks $T(pk, \sigma) = H(m)$. The scheme is existentially unforgeable under chosen-message attacks: for every efficient forger $A$ making at most $Q_{\mathrm{ro}}$ random-oracle queries and $Q_s$ signing queries there is an efficient inverter $B$ in Game 10.2 that is an **elementary wrapper around $A$** (a composition of an efficient interface with $A$, as in Definition 2.12) and satisfies

$$
\mathrm{Adv}^{\mathrm{SIG}}_{\mathrm{ro}}[A] \le (Q_{\mathrm{ro}} + Q_s + 1)\cdot \mathrm{Adv}^{\mathrm{OW}}[B, T].
$$

## Depends on

- [Trapdoor permutations](../hardness-assumptions/trapdoor-permutations.md)
- [One-wayness against efficient interactive adversaries](../hardness-assumptions/interactive-one-wayness.md)
- [Elementary wrappers](../../security-games/asymptotic-security/elementary-wrappers.md)
- [The random oracle model](the-random-oracle-model.md)
- [Signature forgery experiment](../../security-games/generic-security-games/sig-game.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorem 13.3
- M. Bellare and P. Rogaway, "The exact security of digital signatures: how to sign with RSA and Rabin", *EUROCRYPT 1996*, LNCS 1070, Springer, 1996
