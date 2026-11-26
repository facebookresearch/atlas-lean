# Several independent keys of a pseudorandom function

Let $F$ be a PRF and $Q$ a polynomial. An adversary given oracle access to $F(k_1, \cdot), \dots, F(k_Q, \cdot)$ for independent uniform keys distinguishes them from $Q$ independent random functions with advantage at most $Q \cdot \varepsilon$, where $\varepsilon$ is the best PRF advantage of an adversary with comparable running time. Hence $Q$ independent keys of a secure PRF are jointly pseudorandom.

## Proof sketch

Hybrid over the keys: in hybrid $i$ the first $i$ oracles are random functions; the reduction plants its own oracle at a uniformly chosen position and simulates the others.

## Depends on

- [Asymptotic PRF security relative to a class of distinguishers](../pseudorandom-functions/prfsecure.md)

## Proof depends on

- [Hybrid argument](../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
