# Palette sparsification for (deg + 1)-list coloring

Let $G$ be an $n$-vertex graph.

1. For every $\varepsilon > 0$, if $G$ has no isolated vertices and each vertex $v$ (so $\deg(v) \ge 1$) has an arbitrary list of $\lceil (1 + \varepsilon)\deg(v)\rceil$ colors and samples $O_\varepsilon(\log n)$ of them uniformly and independently, then with high probability $G$ is colorable from the samples (an isolated vertex can instead be given a single color and removed before sampling); the same holds, for every graph, with lists $\{1, \dots, \deg(v) + 1\}$ and $O(\log n)$ samples.
2. For arbitrary D1LC lists $S(v)$, sampling $O(\log^2 n)$ colors uniformly and independently from each $S(v)$ makes $G$ colorable from the samples with high probability.

As in the $(\Delta + 1)$ case, this yields a single-pass semi-streaming algorithm for D1LC in dynamic streams, an $O(1)$-round algorithm in the massively parallel computation model with $\widetilde{O}(n)$ memory per machine, and an $\widetilde{O}(n\sqrt{n})$-time algorithm in the query model.

## Proof sketch

The obstacle for D1LC is that low-degree vertices have small lists, so there is no uniform slack. A slack-generation step (a random partial coloring with a constant probability of trying a color) creates, for vertices whose neighborhoods are sparse or whose lists differ from their neighbors' lists, slack proportional to their degree; the remaining vertices form almost-cliques with nearly identical lists. Plugged into the sparse-dense framework of the $(\Delta + 1)$ theorem, these give list-colorability from the samples, with the additional logarithmic factor in part 2 paying for the arbitrary lists.

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
- Maxime Flin, Mohsen Ghaffari, Magnús M. Halldórsson, Fabian Kuhn, Alexandre Nolin, "A Distributed Palette Sparsification Theorem", arXiv:2301.06457 (2023).
