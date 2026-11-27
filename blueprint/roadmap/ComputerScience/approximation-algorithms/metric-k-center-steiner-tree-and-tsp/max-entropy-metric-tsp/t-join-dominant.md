# T-joins and the T-join dominant polyhedron

Let $G=(V,E)$ be an undirected graph and let $T \subseteq V$ with $|T|$ even. A multiset $J$ of edges of $G$ is a $T$-join if the set of vertices of odd degree in the multigraph $(V,J)$ is exactly $T$. A set $S \subseteq V$ is $T$-odd if $|S \cap T|$ is odd. The $T$-join dominant is the polyhedron

$$
P_T^{\uparrow}(G)=\{y \in \mathbb{R}_{\ge 0}^{E} : y(\delta(S)) \ge 1 \ \text{for every}\ T\text{-odd}\ S \subseteq V\}.
$$

Every $T$-join $J$ satisfies $\mathbf{1}_J \in P_T^{\uparrow}(G)$, because a $T$-odd cut contains an odd number of edges of $J$. When $T$ is the set of odd-degree vertices of a spanning tree (an even set by the handshake lemma), a $T$-join is called a parity correction of the tree.

## Depends on

- [Handshake lemma for edge-indexed multigraphs](../../../../GraphTheory/paths-cycles-connectivity/eulerian-circuits/even-sum-degree.md)
- [Edges of a cut](../../primal-dual-method-for-constrained-forests/cut-edges.md)

## Sources

- Jack Edmonds, Ellis L. Johnson, "Matching, Euler Tours and the Chinese Postman", Mathematical Programming (1973).
