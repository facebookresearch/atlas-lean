# Constructing the cactus of all minimum cuts in almost-linear deterministic time

Given a connected undirected graph with $n$ vertices, $m$ edges and positive weights, a cactus representation of all its global minimum cuts can be constructed

1. by a randomized (Monte Carlo) algorithm in $O(m \log^3 n)$ time with success probability $1 - n^{-c}$ (He-Huang-Saranurak, improving the near-linear Monte Carlo construction of Karger-Panigrahi), and
2. by a deterministic algorithm in $m^{1+o(1)}$ time (He-Huang-Saranurak), where the $m^{o(1)}$ factor comes only from deterministic tree packing; previously the fastest explicitly stated deterministic construction took $\tilde O(mn)$ time.

## Proof sketch

Every minimum cut $2$-respects some tree of a small tree family (Karger's skeleton, or Li's deterministic family of $m^{o(1)}$ trees). For a fixed tree, the minimum cuts that $1$- or $2$-respect it are enumerated implicitly through the tree edges that determine them, and the crossing structure given by the corner lemma lets these cuts be merged into cycles and tree edges of a cactus. Combining the per-tree partial cacti along a common refinement yields the cactus of all minimum cuts.

## Depends on

- [Cactus representations of all minimum cuts](cactus-representation-of-minimum-cuts.md)

## Proof depends on

- [Dinits-Karzanov-Lomonosov theorem: every graph has a linear-size cactus of its minimum cuts](dinits-karzanov-lomonosov-cactus-theorem.md)
- [Deterministic almost-linear minimum cut in weighted graphs (Li)](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/deterministic-near-linear-minimum-cut/li-deterministic-almost-linear-weighted-mincut.md)
- [Karger's skeleton: logarithmically many trees one of which 2-respects the minimum cut](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/deterministic-near-linear-minimum-cut/karger-skeleton-tree-family.md)
- [Minimum 2-respecting cut of a spanning tree in O(m log n) deterministic time](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/deterministic-near-linear-minimum-cut/minimum-two-respecting-cut-algorithm.md)

## Sources

- Zhongtian He, Shang-En Huang, Thatchaphol Saranurak, "Cactus Representation of Minimum Cuts: Derandomize and Speed up", SODA (2024), doi:10.1137/1.9781611977912.61, arXiv:2401.10856.
- David R. Karger, Debmalya Panigrahi, "A Near-Linear Time Algorithm for Constructing a Cactus Representation of Minimum Cuts", SODA (2009).
- Jason Li, "Deterministic Mincut in Almost-Linear Time", STOC (2021), arXiv:2106.05513.
