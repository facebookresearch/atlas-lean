# Computational universal hashing implies multi-query security

If $H$ is a computational universal hash function, it is multi-query secure. For an adversary outputting at most $Q$ messages, its success probability is at most $\binom{Q}{2} \le Q^2/2$ times the single-pair success probability of a reduction that runs the adversary and outputs the messages at a uniformly chosen pair of positions $i < j$ of the list.

## Proof sketch

The pair $(i, j)$ is chosen after the list is fixed and independently of the key, so if some distinct pair collides, the chosen pair is a colliding pair with probability at least $1/\binom{Q}{2}$.

## Depends on

- [Computational universal hash function](computational-universal-hash.md)

## Sources

- M. Bellare, "New Proofs for NMAC and HMAC: Security without Collision-Resistance", Journal of Cryptology 28(4), 2015 (proof of the lemma that composing a PRF with a cAU family gives a PRF: the au-adversary outputting a uniformly random pair from the queried list).
