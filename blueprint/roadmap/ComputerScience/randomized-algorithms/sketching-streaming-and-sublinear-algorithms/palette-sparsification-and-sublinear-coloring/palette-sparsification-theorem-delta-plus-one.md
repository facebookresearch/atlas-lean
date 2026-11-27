# Assadi-Chen-Khanna palette sparsification theorem for (Delta + 1)-coloring

For every $c > 0$ there is a constant $C = C(c)$ such that the following holds for every $n$-vertex graph $G$ with maximum degree $\Delta$. If every vertex $v$ independently samples a uniformly random set $L(v)$ of $\min(\Delta + 1, \lceil C\log n\rceil)$ colors from $\{1, \dots, \Delta + 1\}$, then with probability at least $1 - n^{-c}$ the graph $G$ has a proper coloring $\chi$ with $\chi(v) \in L(v)$ for every vertex $v$.

## Proof sketch

Take the sparse-dense decomposition. Sparse vertices are colored first: a random partial coloring using a constant fraction of each list leaves every $\varepsilon$-sparse vertex with $\Omega(\varepsilon^2\Delta)$ repeated colors in its neighborhood, hence slack, and the remaining sampled colors then extend the coloring greedily with high probability. Each almost-clique is then colored through a saturating matching in its palette graph: its $(1 \pm O(\varepsilon))\Delta$ vertices have few outside neighbors, so the available sampled colors behave like independent random subsets of a palette of size at least $|K_i|$, and the matching lemma applies. A union bound over all vertices and almost-cliques finishes the proof.

## Depends on

- [Palette sparsification experiment, sampled lists and the conflict graph](palette-sparsification-experiment.md)

## Proof depends on

- [Sparse-dense decomposition of graphs of maximum degree Delta into sparse vertices and almost-cliques](sparse-dense-decomposition-of-bounded-degree-graphs.md)
- [Almost-cliques are list-colorable from random samples via saturating matchings of the palette graph](almost-cliques-colored-via-palette-graph-matchings.md)
- [$k$-degenerate graphs are $(k + 1)$-colorable](../../../../GraphTheory/graph-coloring/part-01/degeneracy-and-greedy-coloring/colorable.md)

## Sources

- Sepehr Assadi, Yu Chen, Sanjeev Khanna, "Sublinear Algorithms for (Delta + 1) Vertex Coloring", SODA (2019), arXiv:1807.08886.
