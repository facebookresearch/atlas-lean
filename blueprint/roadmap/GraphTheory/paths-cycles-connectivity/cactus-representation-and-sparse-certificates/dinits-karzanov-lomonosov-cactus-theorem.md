# Dinits-Karzanov-Lomonosov theorem: every graph has a linear-size cactus of its minimum cuts

Every connected undirected graph $G$ with $n \ge 2$ vertices and positive edge weights has a cactus representation $(H, \varphi)$ in which $H$ has $O(n)$ nodes and $O(n)$ edges. As a consequence, $G$ has at most $\binom{n}{2}$ global minimum cuts, and for $n \ge 3$ the cycle $C_n$ with unit weights shows that this bound is attained: its minimum cuts are exactly the $\binom{n}{2}$ pairs of edges.

## Proof sketch

Group the minimum cuts into classes of pairwise crossing cuts; by the corner lemma, the members of a maximal crossing class induce a circular partition of $V$ in which every union of consecutive blocks is a minimum cut side, and these become cycles of $H$. Minimum cuts crossing no other minimum cut form a crossing-free family, which is laminar up to complementation and is represented by tree edges. Gluing the cycles and tree edges along the laminar structure yields a cactus with $O(n)$ nodes whose minimum cuts, by the classification of minimum cuts of a cactus, are exactly the minimum cuts of $G$; the count bound follows by maximizing $t + \sum_Z \binom{|Z|}{2}$ over cacti with $n$ nonempty nodes, with the cycle $C_n$ as the extremal case.

## Depends on

- [Cactus representations of all minimum cuts](cactus-representation-of-minimum-cuts.md)

## Proof depends on

- [Corner structure of two crossing minimum cuts](crossing-minimum-cuts-corners.md)
- [Minimum cuts of a weighted cactus are tree edges or pairs of edges on one cycle](cactus-minimum-cuts-classification.md)
- [At most $n(n-1)/2$ minimum cuts](../../../ComputerScience/randomized-algorithms/karger-s-algorithm/two-mul-length-min-cuts-le.md)
- [Crossing pairs of vertex bipartitions](crossing-vertex-bipartitions.md)

## Sources

- Efim A. Dinits, Alexander V. Karzanov, Michael V. Lomonosov, "On the Structure of a System of Minimum Edge Cuts of a Graph", Studies in Discrete Optimization (1976).
- David R. Karger, "Minimum Cuts in Near-Linear Time", Journal of the ACM (2000), arXiv:cs/9812007.
