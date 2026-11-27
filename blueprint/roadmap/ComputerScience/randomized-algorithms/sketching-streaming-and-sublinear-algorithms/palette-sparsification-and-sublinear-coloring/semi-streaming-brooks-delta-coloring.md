# Semi-streaming Brooks theorem: single-pass Delta-coloring

There is a randomized single-pass semi-streaming algorithm that, given an insertion-only edge stream of a connected $n$-vertex graph $G$ with maximum degree $\Delta$ which is neither a clique nor an odd cycle, outputs with high probability a proper coloring of $G$ with $\Delta$ colors. Applied to each connected component, the algorithm either correctly reports that $G$ is not $\Delta$-colorable or outputs a $\Delta$-coloring; the algorithm is implemented with linear sketches and therefore extends to dynamic streams. Palette sparsification alone provably fails for $\Delta$-coloring, so the semi-streaming algorithm needs an additional mechanism, and randomness is necessary.

## Proof sketch

Brooks' theorem guarantees existence. The algorithm samples small palettes as in palette sparsification and, alongside, collects a sparse set of helper edges and structures of almost-cliques computed from sketches. Sparse vertices and almost-cliques with spare structure are colored as in the $(\Delta + 1)$ proof; for the hard almost-cliques, which have exactly $\Delta$ colors available, the algorithm must create one color of slack, in the spirit of Lovász's proof of Brooks' theorem, by coloring suitable non-adjacent vertices identically using the extra stored information.

## Depends on

- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](../semi-streaming-matching-and-vertex-cover/semi-streaming-graph-model.md)

## Proof depends on

- [Brooks' theorem](../../../../GraphTheory/graph-coloring/part-01/brooks.md)
- [Assadi-Chen-Khanna palette sparsification theorem for (Delta + 1)-coloring](palette-sparsification-theorem-delta-plus-one.md)
- [Sparse-dense decomposition of graphs of maximum degree Delta into sparse vertices and almost-cliques](sparse-dense-decomposition-of-bounded-degree-graphs.md)

## Sources

- Sepehr Assadi, Pankaj Kumar, Parth Mittal, "Brooks' Theorem in Graph Streams: A Single-Pass Semi-Streaming Algorithm for Delta-Coloring", STOC (2022), arXiv:2203.10984.
