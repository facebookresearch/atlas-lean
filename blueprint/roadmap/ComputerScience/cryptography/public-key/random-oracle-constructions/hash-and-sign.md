# Hash-and-sign

Let $\mathcal{S}$ be a signature scheme on messages in a set $M$ that is existentially unforgeable under chosen-message attacks, and $H : K_H \times \{0,1\}^* \to M$ a collision-resistant keyed hash family. The scheme whose key generation also samples a uniform hash key $k_H$ and includes it in the public verification key, and which signs $m$ by signing $H(k_H, m)$, is existentially unforgeable under chosen-message attacks: an adversary breaking it yields either a forger for $\mathcal{S}$ or a collision finder for $H$, with advantages adding up. The same holds with a target-collision-resistant hash family $H : K_H \times \{0,1\}^* \to T$, provided the base scheme signs messages in $K_H \times T$: each signature chooses a fresh random hash key $k$ and signs the pair $(k, H(k, m))$.

## Depends on

- [Polynomial-query unforgeability of signatures](../../security-games/asymptotic-security/poly-query-sig-secure.md)

## Expansion

This page becomes ready once:

- Collision resistance and target collision resistance of keyed hash families (statement prerequisite; not yet stated)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorem 13.1
