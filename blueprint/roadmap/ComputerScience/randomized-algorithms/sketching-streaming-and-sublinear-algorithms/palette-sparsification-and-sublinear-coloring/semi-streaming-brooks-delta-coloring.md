# Semi-streaming Brooks theorem: single-pass Delta-coloring

There is a randomized single-pass semi-streaming algorithm that, given an insertion-only edge stream of a connected $n$-vertex graph $G$ with maximum degree $\Delta$ which is neither a clique nor an odd cycle, outputs with high probability a proper coloring of $G$ with $\Delta$ colors. Applied to each connected component, the algorithm either correctly reports that $G$ is not $\Delta$-colorable or outputs a $\Delta$-coloring; the algorithm is implemented with linear sketches and therefore extends to dynamic streams. Palette sparsification alone provably fails for $\Delta$-coloring, so the semi-streaming algorithm needs an additional mechanism, and randomness is necessary.

## Proof sketch

Brooks' theorem guarantees existence. The algorithm samples small palettes as in palette sparsification and, alongside, uses sparse recovery guided by a sparse-dense decomposition to store the almost-cliques that palette sparsification cannot handle, or for the less dense ones small helper structures. Sparse vertices and almost-cliques with enough non-edges are colored from the sampled palettes as in the $(\Delta + 1)$ proof. In a $(\Delta + 1)$-clique minus an edge $\{u, v\}$, the two endpoints get a common color not used outside, and greedy coloring that leaves a common neighbor of $u$ and $v$ for last succeeds. A $\Delta$-clique whose few outside neighbors all received the same color is handled by a recoloring step that changes the colors of some outside vertices, analyzed by splitting the sampling randomness into phases. No local exploration, such as the search for augmenting paths, is needed.

## Depends on

- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](../semi-streaming-matching-and-vertex-cover/semi-streaming-graph-model.md)

## Proof depends on

- [Brooks' theorem](../../../../GraphTheory/graph-coloring/part-01/brooks.md)
- [Assadi-Chen-Khanna palette sparsification theorem for (Delta + 1)-coloring](palette-sparsification-theorem-delta-plus-one.md)
- [Sparse-dense decomposition of graphs of maximum degree Delta into sparse vertices and almost-cliques](sparse-dense-decomposition-of-bounded-degree-graphs.md)

## Sources

- Sepehr Assadi, Pankaj Kumar, Parth Mittal, "Brooks' Theorem in Graph Streams: A Single-Pass Semi-Streaming Algorithm for Delta-Coloring", STOC (2022); TheoretiCS 2 (2023), Article 9, arXiv:2203.10984.
