# The random oracle model

Let $S$ be a cryptographic scheme, indexed by a security parameter $\lambda$, that evaluates a hash function $H$ from a finite set $M_\lambda$ to a finite nonempty set $T_\lambda$ only as an oracle, and let a security property of $S$ be given by an attack game between a challenger and an adversary. The random oracle version of the game is obtained as follows.

- At the beginning of the game the challenger chooses a function $O$ uniformly at random from the set of all functions $M_\lambda \to T_\lambda$.
- In processing its standard queries the challenger evaluates $O$ in place of $H$.
- In addition to its standard queries, the adversary may submit any number of random oracle queries $m \in M_\lambda$, arbitrarily interleaved with standard queries, each answered by $O(m)$.

The advantage of an adversary is defined by the same rule as in the original game, and $S$ is *secure in the random oracle model* if this advantage is negligible in $\lambda$ for all [efficient adversaries](../../security-games/asymptotic-security/efficient-adversaries.md). The function $O$, one uniformly random function shared by the challenger and the adversary, is the *random oracle*. Security in this model is a heuristic for the scheme with a concrete hash function: it rules out generic attacks, those that would succeed if $H$ were a random oracle, but guarantees nothing for a particular hash function.

For a single oracle computation, answering each fresh query with an independent uniform element of $T_\lambda$ and recording it gives the same output distribution as querying a function drawn uniformly in advance.

## Depends on

- [Adaptive oracle algorithms](../../security-games/oracle-algorithms/oracle-comp.md)
- [Efficient adversaries](../../security-games/asymptotic-security/efficient-adversaries.md)

## Proof depends on

- [Lazy random functions are random functions](../../security-games/lazy-sampling-and-the-prp-prf-switching-lemma/lazy-rf-map-fst.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Section 8.10.2
