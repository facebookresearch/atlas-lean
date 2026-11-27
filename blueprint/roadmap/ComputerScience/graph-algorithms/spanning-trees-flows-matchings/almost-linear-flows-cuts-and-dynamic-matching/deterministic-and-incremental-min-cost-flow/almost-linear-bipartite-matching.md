# Maximum bipartite matching and weighted assignment in almost-linear time

There is a deterministic algorithm that computes a maximum-cardinality matching in a bipartite graph with $m$ edges in $m^{1+o(1)}$ time. More generally, for a bipartite graph with integral edge costs bounded by $C$ and vertex degree bounds $\mathbf{b}_v \le U$, a minimum-cost $\mathbf{b}$-matching or worker assignment is computed in $m^{1+o(1)}\log U\log C$ time, and transportation problems with integral supplies are solved within the same bound.

## Proof sketch

Orient edges from the left side $V_1$ to the right side $V_2$ with capacity $1$, add a source joined to $V_1$ and a sink joined from $V_2$ with unit capacities (or capacities $\mathbf{b}_v$), and solve the resulting flow problem by *Deterministic minimum-cost flow in almost-linear time*. Integral optimal flows correspond to matchings of the same size or cost by integrality of flows, and maximality is certified by a minimum cut, equivalently a minimum vertex cover by Konig's theorem.

## Depends on

- [Matching in a bipartite graph](../../maximum-bipartite-matching/is-matching.md)

## Proof depends on

- [Deterministic minimum-cost flow in almost-linear time](deterministic-almost-linear-min-cost-flow.md)
- [Integral flow theorem](../../edmonds-karp-algorithm/exists-nat-max-flow.md)
- [Kőnig's theorem for finite bipartite graphs](../../../../../GraphTheory/matchings-and-flows/k-nig-s-theorem/konig-matching-cover.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
