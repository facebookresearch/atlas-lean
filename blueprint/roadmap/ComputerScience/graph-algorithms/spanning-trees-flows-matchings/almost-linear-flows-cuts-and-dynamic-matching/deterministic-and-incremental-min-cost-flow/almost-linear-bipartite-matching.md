# Maximum bipartite matching and weighted assignment in almost-linear time

There is a deterministic algorithm that computes a maximum-cardinality matching in a bipartite graph with $m$ edges in $m^{1+o(1)}$ time. More generally, let $G = (V_1 \cup V_2, E)$ be bipartite with integral edge costs bounded by $C$ in absolute value, integral edge capacities $\mathbf{u}_e \in \{0, \ldots, U\}$ and integral vertex demands $\mathbf{b}_v \in \{0, \ldots, U\}$. In $m^{1+o(1)}\log U\log C$ time the algorithm either computes a minimum-cost worker assignment, an integral $\mathbf{w} \in \mathbb{Z}^E$ with $\mathbf{0} \le \mathbf{w} \le \mathbf{u}$ whose total weight at every vertex $v$ is exactly $\mathbf{b}_v$, or reports that none exists; a minimum-cost perfect $\mathbf{b}$-matching is the case $\mathbf{u} = \mathbf{1}$. A transportation problem with integral supplies $\mathbf{b}_v$ on $V_1$ and integral demands $\mathbf{b}_v$ on $V_2$, all at most $U$, is the case $\mathbf{u}_{e} = \min\{\mathbf{b}_v, \mathbf{b}_{v'}\}$ for $e = vv'$, since no edge needs to ship more than that; it is reported infeasible when, for instance, total supply and total demand differ.

## Proof sketch

For a maximum matching, orient each edge from $V_1$ to $V_2$ with capacity $1$, add a source with a unit-capacity arc to every vertex of $V_1$ and a sink with a unit-capacity arc from every vertex of $V_2$, and compute an integral maximum flow by *Deterministic minimum-cost flow in almost-linear time*. An integral flow of value $k$ is exactly a matching of size $k$, so the maximum flow value is the maximum matching size, and maximality is certified by a minimum cut, equivalently a minimum vertex cover by Kőnig's theorem. For a worker assignment, orient each edge from $V_1$ to $V_2$ with capacity $\mathbf{u}_e$ and cost $\mathbf{c}_e$, and give every $v \in V_1$ supply $\mathbf{b}_v$ and every $v \in V_2$ demand $\mathbf{b}_v$; the integral feasible flows are exactly the worker assignments, with the same cost, so the algorithm returns an integral optimum or reports that the demands cannot be met.

## Depends on

- [Matching in a bipartite graph](../../maximum-bipartite-matching/is-matching.md)

## Proof depends on

- [Deterministic minimum-cost flow in almost-linear time](deterministic-almost-linear-min-cost-flow.md)
- [Integral flow theorem](../../edmonds-karp-algorithm/exists-nat-max-flow.md)
- [Kőnig's theorem for finite bipartite graphs](../../../../../GraphTheory/matchings-and-flows/k-nig-s-theorem/konig-matching-cover.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
