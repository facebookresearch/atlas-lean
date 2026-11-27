# Gale's feasibility condition for transportation problems

Let finitely many sources have supplies $a_i \ge 0$ and finitely many destinations demands $d_j \ge 0$ with $\sum_i a_i = \sum_j d_j$, and let $E$ be a set of allowed source–destination pairs. There is a shipment $x \ge 0$ supported on $E$ meeting all supplies and demands exactly if and only if for every set $D$ of destinations, $\sum_{j \in D} d_j \le \sum_{i \in N(D)} a_i$, where $N(D)$ is the set of sources with an allowed pair into $D$. When these inequalities hold and the data are integral, there is an integral shipment, and for any real costs $c_{ij}$ on $E$ the minimum of $\sum c_{ij}x_{ij}$ over feasible shipments is attained at an integral shipment; integral data alone do not give feasibility. The constraint matrix, after negating the source rows, is the incidence matrix of the bipartite directed graph of allowed pairs.

## Proof depends on

- [Hoffman's circulation theorem](hoffman-circulation-theorem.md): feasibility: the bipartite network with supplies and demands as net flows and an arc of capacity $\sum_i a_i$ for each allowed pair.
- [Totally unimodular systems have integral vertices](../../../Geometry/convex-geometry/total-dual-integrality/totally-unimodular-systems-have-integral-vertices.md): integral minimum-cost shipments: the transportation matrix is the incidence matrix of a directed graph.

## Sources

- A. Schrijver, *A Course in Combinatorial Optimization*, lecture notes, CWI and University of Amsterdam, 2017, <https://homepages.cwi.nl/~lex/files/dict.pdf>, §4.5, Theorems 4.6–4.7, and §8.4, Theorem 8.4 and Corollary 8.1b
