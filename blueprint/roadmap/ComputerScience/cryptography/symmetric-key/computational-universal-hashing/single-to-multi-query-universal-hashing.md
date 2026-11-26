# Computational universal hashing implies multi-query security

If $H$ is a computational universal hash function, it is multi-query secure. For an adversary outputting at most $Q$ messages, its success probability is at most $\binom{Q}{2} \le Q^2/2$ times the single-pair success probability of a reduction that outputs a uniformly chosen ordered pair of positions from the list.

## Proof sketch

If some distinct pair collides, a uniformly random pair of positions hits a colliding pair with probability at least $1/\binom{Q}{2}$.

## Depends on

- [Computational universal hash function](computational-universal-hash.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
