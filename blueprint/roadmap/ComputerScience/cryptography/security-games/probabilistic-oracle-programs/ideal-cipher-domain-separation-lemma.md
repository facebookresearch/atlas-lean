# Domain separation lemma for the ideal cipher

Let $U, V, X$ be finite sets and $f : U \to V$. In the *coalesced* experiment an adversary makes adaptive forward and inverse queries $(\mu, \pm, z)$ with $\mu \in U$, answered by a family of independent random permutations $(\pi_v)_{v \in V}$ of $X$ via $\pi_{f(\mu)}$, so keys in one fiber of $f$ share a permutation. In the *split* experiment every $\mu \in U$ has its own independent random permutation $\pi'_\mu$. Then the distinguishing advantage between the two experiments is at most the probability, in the split experiment, that two queries with distinct keys $\mu \ne \mu'$ in the same fiber of $f$ produce a common input or a common output value across their partial permutations.

## Proof sketch

Run both experiments with lazily sampled permutations and flag the first cross-key collision within a fiber; until that event the coalesced permutation restricted to each key's queries is distributed as an independent random injection, so the two experiments are identical until bad.

## Depends on

- [Ideal cipher model](ideal-cipher-model.md)

## Proof depends on

- [Fundamental lemma of game playing for stateful oracle handlers](../identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
