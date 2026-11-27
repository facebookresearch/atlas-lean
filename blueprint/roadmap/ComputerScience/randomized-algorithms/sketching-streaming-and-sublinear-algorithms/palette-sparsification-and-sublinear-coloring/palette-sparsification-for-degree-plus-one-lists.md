# Palette sparsification for (deg + 1)-list coloring

Let $G$ be an $n$-vertex graph, and let every vertex $v$ sample a set $L(v)$ of $\ell$ colors uniformly at random from its list $S(v)$, independently of the other vertices.

1. For every $\varepsilon > 0$ (not necessarily constant), if $G$ has no isolated vertices and each $S(v)$ is an arbitrary set of $(1 + \varepsilon)\deg(v)$ colors, then $\ell = \Theta(\varepsilon^{-1}\log n)$ samples make $G$ colorable from the lists $L(v)$ with high probability (an isolated vertex can instead be given a single color and removed before sampling); the same holds, for every graph, with $S(v) = \{1, \dots, \deg(v) + 1\}$ and $\ell = \Theta(\log n)$.
2. If each $S(v)$ is an arbitrary set of exactly $\deg(v) + 1$ colors, then $\ell = \Theta(\log^2 n)$ samples make $G$ colorable from the lists $L(v)$ with high probability.

As in the $(\Delta + 1)$ case, part 2 yields, with high probability, a single-pass semi-streaming algorithm for D1LC in dynamic streams, an $O(1)$-round algorithm in the massively parallel computation model with $\widetilde{O}(n)$ memory per machine, and a non-adaptive $\widetilde{O}(n\sqrt{n})$-time algorithm in the query model.

## Proof sketch

The first case of part 1 is a direct greedy argument: in any vertex order, at most $\deg(v)$ colors of $S(v)$ are blocked when $v$ is processed, so each sample is unblocked with probability at least $\varepsilon/(1 + \varepsilon)$, and $\Theta(\varepsilon^{-1}\log n)$ samples all miss with probability $n^{-\Omega(1)}$. For the other cases low-degree vertices have small lists and no uniform slack, so the proof follows the sparse-dense approach of the $(\Delta + 1)$ theorem with a weaker decomposition adapted to unequal degrees: vertices with sparse neighborhoods, or with lists that differ from their neighbors' lists, obtain slack from a random partial coloring, and the remaining vertices form almost-cliques colored through matchings in their palette graphs. For part 2 the slack-generation step needs degrees of order $\log^2 n$ to hold with high probability, which is where the larger sample size comes from; vertices of smaller degree are colored last.

## Depends on

- [The (deg + 1)-list-coloring problem (D1LC)](degree-plus-one-list-coloring.md)
- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](../semi-streaming-matching-and-vertex-cover/semi-streaming-graph-model.md)
- [The massively parallel computation model](../../../parallel-algorithms/massively-parallel-computation-graph-algorithms/massively-parallel-computation-model.md)

## Proof depends on

- [Assadi-Chen-Khanna palette sparsification theorem for (Delta + 1)-coloring](palette-sparsification-theorem-delta-plus-one.md)
- [Sparse-dense decomposition of graphs of maximum degree Delta into sparse vertices and almost-cliques](sparse-dense-decomposition-of-bounded-degree-graphs.md)
- [Almost-cliques are list-colorable from random samples via saturating matchings of the palette graph](almost-cliques-colored-via-palette-graph-matchings.md)

## Sources

- Noga Alon, Sepehr Assadi, "Palette Sparsification Beyond (Delta+1) Vertex Coloring", APPROX/RANDOM (2020), arXiv:2006.10456.
- Magnús M. Halldórsson, Fabian Kuhn, Alexandre Nolin, Tigran Tonoyan, "Near-Optimal Distributed Degree+1 Coloring", STOC (2022), arXiv:2112.00604.
