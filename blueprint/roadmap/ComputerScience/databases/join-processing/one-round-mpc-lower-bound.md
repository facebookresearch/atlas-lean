# One-round MPC lower bound

This node collects the one-round lower bound of Beame, Koutris and Suciu for connected, full,
self-join-free conjunctive queries in the MPC model. A conjunctive query is full when every body variable
appears in the head, self-join-free when each relation name occurs at most once, and connected when its
hypergraph is connected.

## Expansion

A sound expansion has separate pages for:

1. **Input distribution.** Matching databases: every relation of arity $r$ is a uniformly random
   $r$-dimensional matching on $[n]$.
2. **Lower bound.** Let $q$ be a connected, full, self-join-free query with fractional vertex cover
   number $\tau^*(q)$ and let $\varepsilon < 1 - 1/\tau^*(q)$. Every deterministic one-round algorithm in the
   MPC($\varepsilon$) model on $p$ servers reports, in expectation over a uniformly random matching
   database, $O\bigl(\mathbb{E}[\lvert q(I) \rvert] / p^{\tau^*(q)(1-\varepsilon)-1}\bigr)$ answers (Theorem 3.3), with
   $\mathbb{E}[\lvert q(I) \rvert]$ given by Lemma 3.4. By Yao's principle, every randomized one-round
   MPC($\varepsilon$) algorithm computing $q$ has space exponent $\varepsilon \ge 1 - 1/\tau^*(q)$, even on
   matching databases (Theorem 1.1), with the source's load and failure-probability conventions.
3. **Matching upper bound** on matching databases by the HyperCube algorithm with share exponents
   proportional to an optimal fractional vertex cover (Proposition 3.2), as a separate page.

## Depends on

- [MPC(eps) model](mpc-model.md)
- [Matching databases](matching-databases.md)
- [Query hypergraph and fractional vertex covering number](query-hypergraph-and-fractional-vertex-covering-number.md)

## Sources

- Communication Steps for Parallel Query Processing (Beame, Koutris, Suciu, PODS 2013) — Beame, Koutris, Suciu; ACM PODS, author copy, Theorem 1.1, Proposition 3.2, Theorem 3.3 and Lemma 3.4. <https://homes.cs.washington.edu/~beame/papers/mpcpods.pdf>
