# Zig-zag product and explicit expanders

Regular multigraphs given by rotation maps, and the graph operations that build constant-degree expanders from a single small one: squaring, which squares the spectral parameter and the degree, and the zig-zag product of Reingold, Vadhan and Wigderson, whose result inherits its size from a big graph, its degree from a small graph and its expansion from both.

- [Rotation map of a regular multigraph](rotation-map.md)
- [Adjacency matrix of a rotation map](adj-matrix.md)
- [The adjacency matrix acts by summing over labels](adj-matrix-mul-vec-apply.md)
- [Rows of the adjacency matrix sum to the degree](adj-matrix-mul-vec-one.md)
- [The adjacency matrix of a rotation map is symmetric](adj-matrix-transpose.md)
- [$(N, D, \lambda)$-graph given by a rotation map](is-ndlambda-graph.md)
- [Every rotation map gives an $(N, D, 1)$-graph](is-ndlambda-graph-one.md)
- [Square of a rotation map](square.md)
- [Adjacency matrix of the square](adj-matrix-square.md)
- [Squaring squares the spectral parameter](is-ndlambda-graph-square.md)
- [Zig-zag product of rotation maps](zigzag.md)
- [Norm bound from a quadratic-form bound](quadratic-form-bound-gives-norm-bound.md)
- [Zig-zag theorem](zig-zag-theorem.md)
- [Zig-zag theorem, spectral-gap form](zig-zag-theorem-gap-form.md)
- [Relabelling the edges of a rotation map](relabel.md)
- [Relabelling preserves the adjacency matrix](adj-matrix-relabel.md)
- [Relabelling preserves the $(N, D, \lambda)$ property](is-ndlambda-graph-relabel.md)
- [The $(N, D, \lambda)$ property is monotone in $\lambda$](is-ndlambda-graph-mono.md)
- [Vertex types of the zig-zag family](zig-zag-family-vertex.md)
- [The zig-zag expander family](zigzag-family.md)
- [Size of the zig-zag expander family](card-zigzag-family-vertex.md)
- [The zig-zag expander family consists of expanders](is-ndlambda-graph-zigzag-family.md)

## Related topics

- [Expander graphs](../expander-graphs/README.md): spectral expansion for simple graphs, the expander mixing lemma, the Alon-Boppana bound and random walks on expanders.
- [Finite multigraphs](../finite-multigraphs/README.md): multigraphs given by edge endpoint maps, the encoding used for Laplacians and Cheeger's inequality; a rotation map lists the same edges by their labels at both endpoints.
- [Undirected s-t connectivity](../../../TheoryOfComputation/polynomial-time-problems/undirected-s-t-connectivity/README.md): Reingold's log-space algorithm turns each connected component into an expander by repeated squaring and zig-zag products.
