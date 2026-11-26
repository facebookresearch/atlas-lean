# Pair-layer graphs

The graph with initial order $m$ and depth $d$ has layers $L_0,\ldots,L_d$. The set $L_0$ has $m$ vertices, and each $L_{i+1}$ consists of the unordered two-element subsets of $L_i$, regarded as vertices in a new disjoint layer. There is an edge only from such a vertex to each of its two parents. In particular, $|L_{i+1}|=\binom{|L_i|}{2}$, and the graph is simple and bipartite by parity of the layer. Its definition does not depend on the labeling of the layer vertices.

## Sources

- [Pair-layer constructors, parents and adjacency](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L11979-L12153)
