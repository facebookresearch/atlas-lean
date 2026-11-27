# Effect of overwriting one entry of a memoized random oracle

Let $A$ be an oracle program run against a lazily sampled (memoized) random function $O$, and let $O'$ be the oracle obtained by fixing the value at one point $x^*$ to some $y^*$ (possibly overwriting an existing cache entry with a different value). Then for every event $E$ on the visible output of $A$ (the cache being projected away),

$$\Pr[A^{O'} \in E] \le \Pr[A^{O} \in E] + \Pr[A^{O} \text{ queries } x^*].$$

## Proof sketch

The two runs are identical until the first query to $x^*$; mark that query as the bad event and apply the fundamental lemma of game playing, computing the bad probability in the unmodified run.

## Depends on

- [Lazy random function](../lazy-sampling-and-the-prp-prf-switching-lemma/lazy-rf.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Proof depends on

- [Fundamental lemma of game playing for stateful oracle handlers](fundamental-lemma-for-stateful-handlers.md)

## Sources

- M. Bellare and P. Rogaway, "Random Oracles are Practical: A Paradigm for Designing Efficient Protocols", Proceedings of the 1st ACM Conference on Computer and Communications Security (CCS), 1993.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
