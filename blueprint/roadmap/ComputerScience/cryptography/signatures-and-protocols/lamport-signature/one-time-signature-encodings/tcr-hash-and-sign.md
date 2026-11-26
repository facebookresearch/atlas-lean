# Signing a fresh target collision-resistant hash extends signatures to long messages

Let $S$ be an EUF-CMA secure signature scheme on short messages and $H$ a target collision-resistant keyed hash family. The scheme that signs $m$ by choosing a fresh uniform hash key $r$ and outputting $(r, \sigma)$ with $\sigma = S(sk, (r, H_r(m)))$, and verifies $\sigma$ on $(r, H_r(m))$, is EUF-CMA secure on messages of arbitrary length.

## Proof sketch

A forgery $(m^*, r^*, \sigma^*)$ either signs a pair $(r^*, H_{r^*}(m^*))$ never signed before, a forgery against $S$, or reuses a pair from the $i$-th signing query, so that $H_{r_i}(m^*) = H_{r_i}(m_i)$ with $m^* \ne m_i$; the TCR adversary guesses $i$, commits to $m_i$ before receiving $r_i$, and outputs $m^*$.

## Depends on

- [Signature forgery experiment](../../../security-games/generic-security-games/sig-game.md)
- [Collision resistance and target collision resistance](../../../hash-functions/collision-resistance-and-target-collision-resistance.md)

## Proof depends on

- [Hash-and-sign](../../../public-key/random-oracle-constructions/hash-and-sign.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Naor and M. Yung, "Universal One-Way Hash Functions and their Cryptographic Applications", Proceedings of the 21st Annual ACM Symposium on Theory of Computing (STOC), 1989.
