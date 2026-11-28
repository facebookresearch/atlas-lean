# Palette sparsification for (deg + 1)-list coloring

Let $G$ be an $n$-vertex graph, and let every vertex $v$ sample a set $L(v)$ of $\min\{\ell, |S(v)|\}$ colors uniformly at random from its list $S(v)$, independently of the other vertices; a vertex whose list has at most $\ell$ colors keeps its whole list.

1. For every $0 < \varepsilon \le 1$ (not necessarily constant), if $G$ has no isolated vertices and each $S(v)$ is an arbitrary set of at least $(1 + \varepsilon)\deg(v)$ colors, then $\ell = \Theta(\varepsilon^{-1}\log n)$ samples make $G$ colorable from the lists $L(v)$ with high probability (an isolated vertex can instead be given a single color and removed before sampling); the same holds, for every graph, with $S(v) = \{1, \dots, \deg(v) + 1\}$ and $\ell = \Theta(\log n)$.
2. If each $S(v)$ is an arbitrary set of exactly $\deg(v) + 1$ colors, then $\ell = \Theta(\log^2 n)$ samples make $G$ colorable from the lists $L(v)$ with high probability.

Since the lists are part of the D1LC input and an edge stream alone does not determine the color names, the algorithms obtained from part 2 receive the lists explicitly. As in the $(\Delta + 1)$ case, part 2 yields, with high probability, a single-pass semi-streaming algorithm for D1LC in dynamic streams in which the palettes are given as part of the stream, the final palette of each vertex appearing before the first occurrence of an edge incident to it (the palette is then sampled with $L_0$-samplers); an $O(1)$-round algorithm in the massively parallel computation model with $\widetilde{O}(n)$ memory per machine; and a non-adaptive $\widetilde{O}(n\sqrt{n})$-time algorithm in a query model with two kinds of queries, the $i$-th neighbor of a vertex $v$ and the $i$-th color in the palette $S(v)$ (each answered by a special symbol when $i$ exceeds $\deg(v)$, respectively $|S(v)|$).

## Proof sketch

The first case of part 1 is a direct greedy argument: in any vertex order, at most $\deg(v)$ colors of $S(v)$ are blocked when $v$ is processed, so a uniformly random $\ell$-subset of $S(v)$ lies inside the blocked colors with probability at most $(1/(1 + \varepsilon))^{\ell} \le (1 - \varepsilon/2)^{\ell}$, using $\varepsilon \le 1$, which is $n^{-\Omega(1)}$ for $\ell = \Theta(\varepsilon^{-1}\log n)$; a vertex that keeps its whole list has an unblocked color outright. The cap $\varepsilon \le 1$ matters: on a perfect matching whose two endpoints share the same list of $1 + \varepsilon$ colors, with $\varepsilon = \lceil\log^2 n\rceil$, the prescribed $\Theta(\varepsilon^{-1}\log n)$ samples are at most one per vertex for large $n$, and then some of the $n/2$ edges receives the same color at both ends with probability tending to $1$. For the other cases low-degree vertices have small lists and no uniform slack, so the proof follows the sparse-dense approach of the $(\Delta + 1)$ theorem with a weaker decomposition adapted to unequal degrees: vertices with sparse neighborhoods, or with lists that differ from their neighbors' lists, obtain slack from a random partial coloring, and the remaining vertices form almost-cliques colored through matchings in their palette graphs. For part 2 the slack-generation step needs degrees of order $\log^2 n$ to hold with high probability, which is where the larger sample size comes from; vertices of smaller degree are colored last.

## Depends on

- [The (deg + 1)-list-coloring problem (D1LC)](degree-plus-one-list-coloring.md)
- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](../semi-streaming-matching-and-vertex-cover/semi-streaming-graph-model.md)
- [The massively parallel computation model](../../../parallel-algorithms/massively-parallel-computation-graph-algorithms/massively-parallel-computation-model.md)

## Proof depends on

- [Assadi-Chen-Khanna palette sparsification theorem for (Delta + 1)-coloring](palette-sparsification-theorem-delta-plus-one.md)
- [Sparse-dense decomposition of graphs of maximum degree Delta into sparse vertices and almost-cliques](sparse-dense-decomposition-of-bounded-degree-graphs.md)
- [Almost-cliques are list-colorable from random samples via saturating matchings of the palette graph](almost-cliques-colored-via-palette-graph-matchings.md)

## Sources

- Noga Alon, Sepehr Assadi, "Palette Sparsification Beyond (Delta+1) Vertex Coloring", APPROX/RANDOM (2020), arXiv:2006.10456, Theorem 3 and Section 4.1.
- Magnús M. Halldórsson, Fabian Kuhn, Alexandre Nolin, Tigran Tonoyan, "Near-Optimal Distributed Degree+1 Coloring", STOC (2022), arXiv:2112.00604, Theorem 4, Corollary 3 and Section 8.
