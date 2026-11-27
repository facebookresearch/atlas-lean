# The Naor–Reingold function is a PRF under DDH

If the decisional Diffie–Hellman assumption holds for the group family, then the Naor–Reingold function is a pseudorandom function into the group. For an adversary making $Q$ queries, $\mathrm{PRFadv} \le n \cdot \mathrm{MultiDDHadv}$ for a multi-DDH distinguisher with $Q$ pairs; composing with a universal hash gives a bit-string PRF.

## Proof sketch

Hybrid over the bit positions: in hybrid $j$ the exponent $a_0\prod_{i\le j, x_i=1} a_i$ is replaced by a lazily sampled random function of the prefix $x_{1..j}$. Moving from $j-1$ to $j$ is exactly a multi-DDH instance $(g^{r}, g^{r a_j})$ for the random values $r$, which reduces to DDH by random self-reducibility.

## Depends on

- [Naor–Reingold pseudorandom function](naor-reingold-prf.md)
- [Advantage of a DDH distinguisher](../../public-key/elgamal-encryption/ddh-advantage.md)
- [Asymptotic PRF security relative to a class of distinguishers](../pseudorandom-functions/prfsecure.md)

## Proof depends on

- [Multi-DDH from DDH](../../public-key/discrete-logarithm-and-diffie-hellman-problems/random-self-reducibility-of-diffie-hellman-problems/multi-ddh-from-ddh.md)
- [Lazy random function](../../security-games/lazy-sampling-and-the-prp-prf-switching-lemma/lazy-rf.md)

## Sources

- M. Naor and O. Reingold, "Number-Theoretic Constructions of Efficient Pseudo-Random Functions", Journal of the ACM 51(2), 2004.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
