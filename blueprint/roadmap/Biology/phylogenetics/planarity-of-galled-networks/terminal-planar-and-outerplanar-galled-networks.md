# Terminal planar and outerplanar galled networks

**Setting.** A binary phylogenetic network $N$ on a leaf set $X$ is a rooted acyclic digraph with a root $\rho$ of in-degree $0$ and out-degree $1$, leaves of in-degree $1$ and out-degree $0$ bijectively labeled by $X$, tree vertices of in-degree $1$ and out-degree $2$, and reticulation vertices of in-degree $2$ and out-degree $1$; $\overline N$ denotes its underlying undirected graph. A *galled cycle* is a subgraph formed by two internally disjoint directed paths from a common tree vertex (its top) to a common reticulation $r$ in which every vertex other than $r$ is a tree vertex. $N$ is a *galled network* if every reticulation lies in a unique galled cycle. Planarity notions refer to $\overline N$: $N$ is *planar* if $\overline N$ has a planar drawing, *upward planar* if it has a planar drawing in which every arc is drawn monotonically upward, *terminal planar* if it has a planar drawing with $\rho$ and all leaves on the outer face, and *outerplanar* if it has a planar drawing with every vertex on the outer face.

Two overlapping galled cycles meet in a single tree path, their *intersecting path*. A tree vertex $v$ is *primitive* if it is an internal vertex of the intersecting path of two distinct galled cycles. A tree vertex $v$ with neighbours $v_1,v_2,v_3$ is *separable* if it lies in exactly three galled cycles $G_1,G_2,G_3$ with $v_i\notin V(G_i)$ for $i=1,2,3$.

**Statement.** Let $N$ be a galled network.

1. $N$ is terminal planar if and only if it contains no primitive tree vertex; equivalently, if and only if $\overline N$ contains no normal pivotal subdivision of $K_{2:3}$.
2. $N$ is outerplanar if and only if it contains neither a primitive nor a separable tree vertex; equivalently, if and only if $\overline N$ contains no normal subdivision of $K_{2,3}$ (a subdivision whose three branch paths are tree paths).
3. Both properties have finite forbidden-subgraph characterisations: $N$ is terminal planar if and only if it contains no directed subdivision of two small galled networks $D_1,D_2$ (each containing a primitive vertex), and outerplanar if and only if it contains no directed subdivision of $D_1$, $D_2$ or a third network $D_3$ containing a separable vertex.

## Depends on

- [Planar galled networks are upward planar](planar-galled-networks-are-upward-planar.md)

## Expansion

For general graphs, outerplanarity is excluded by subdivisions of $K_4$ and $K_{2,3}$. In a galled network the degree-$3$ branch vertices of any $2$-connected subgraph are tree vertices, and subdivisions of $K_4$ force subdivisions of $K_{2,3}$, so only $K_{2,3}$ matters; any such subdivision can be rerouted to a normal one using the cut-edge structure below reticulations. Two galled cycles sharing a path with an internal tree vertex $v$ form a $K_{2,3}$ subdivision with branch vertices at the ends of the shared path and $v$, $r_1$, $r_2$ in the middle, which is a primitive configuration; the remaining normal $K_{2,3}$ subdivisions arise from three galled cycles meeting at a single separable vertex. For terminal planarity of a general network, the obstructions are a subdivision of $K_{3,3}$ and pivotal subdivisions of $K_{2:3}$ and $K_{4:2}$ (subdivisions whose designated branch vertices can be joined, by pairwise disjoint paths leaving the subgraph, to cut vertices of $\overline N$); on galled networks the first and last force the second, and a pivotal $K_{2:3}$ can be made normal, which leaves exactly the primitive configurations. Since primitive and separable vertices are defined from galled cycles alone, both properties can be checked directly from the cycle structure of $N$.

## Sources

- Hexuan Liu, Taoyang Wu, Guan-Ru Yu, "Characterisations of Planar Galled Networks", arXiv:2609.28597 (2026), Theorem 4, Theorem 5, Theorem 6, Theorem 7, Theorem 8, Theorem 9 and Theorem 10, <https://doi.org/10.48550/arXiv.2609.28597>
