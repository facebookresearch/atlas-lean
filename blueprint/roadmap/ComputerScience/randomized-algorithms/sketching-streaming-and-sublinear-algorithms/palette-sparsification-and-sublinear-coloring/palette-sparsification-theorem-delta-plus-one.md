# Assadi-Chen-Khanna palette sparsification theorem for (Delta + 1)-coloring

There is an absolute constant $C$ such that the following holds for every $n$-vertex graph $G$ with maximum degree $\Delta$. If every vertex $v$ independently samples a uniformly random set $L(v)$ of $\min(\Delta + 1, \lceil C\log n\rceil)$ colors from $\{1, \dots, \Delta + 1\}$, then with high probability, that is with probability $1 - 1/\mathrm{poly}(n)$, the graph $G$ has a proper coloring $\chi$ with $\chi(v) \in L(v)$ for every vertex $v$. The order $\log n$ of the sample size is necessary.

## Proof sketch

Take the sparse-dense decomposition and split each list into three independent batches. With the first batch, a random partial coloring leaves every sparse vertex with $\Omega(\varepsilon^2\Delta)$ colors repeated in its neighborhood, hence slack, and the remaining sampled colors of the batch complete the sparse vertices greedily with high probability. With the second batch, each almost-clique with $\bar d$ non-edges per vertex on average colors $\Theta(\bar d)$ pairs of non-adjacent vertices with a common color (a colorful matching), saving colors. With the third batch, the remaining vertices of each almost-clique are colored through a saturating matching in its palette graph: they are at most $(1 - 3\delta)N$ for a suitable $N$, each has at least $2N/3$ available colors and on average $(1 - \delta)N$ of them, so the large-matching lemma for randomly sparsified bipartite graphs applies. A union bound over all vertices and almost-cliques finishes the proof.

## Depends on

- [Palette sparsification experiment, sampled lists and the conflict graph](palette-sparsification-experiment.md)

## Proof depends on

- [Sparse-dense decomposition of graphs of maximum degree Delta into sparse vertices and almost-cliques](sparse-dense-decomposition-of-bounded-degree-graphs.md)
- [Almost-cliques are list-colorable from random samples via saturating matchings of the palette graph](almost-cliques-colored-via-palette-graph-matchings.md)
- [$k$-degenerate graphs are $(k + 1)$-colorable](../../../../GraphTheory/graph-coloring/part-01/degeneracy-and-greedy-coloring/colorable.md)

## Sources

- Sepehr Assadi, Yu Chen, Sanjeev Khanna, "Sublinear Algorithms for (Delta + 1) Vertex Coloring", SODA (2019), arXiv:1807.08886.
