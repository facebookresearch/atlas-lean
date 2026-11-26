# Minimal binary level-5 networks that are not tree-based

**Setting.** An **unrooted phylogenetic network** on a finite set $X$ is a connected simple graph with no degree-two vertices whose degree-one vertices (leaves) are bijectively labelled by $X$; it is binary if every inner vertex has degree $3$. It is **tree-based** if it has a spanning tree whose leaf set is exactly $X$ (a support tree). A *blob* is a maximal connected subgraph without cut edges, and a network is **proper** if removing any cut edge or cut vertex leaves components that each contain a leaf. A network is level-$k$ if at most $k$ edges must be removed from each blob to obtain a tree.

**Parity.** Every cubic graph has an even number of vertices, and every unrooted binary phylogenetic network with $n>1$ leaves has an even number of vertices (Proposition 1).

**Theorem 2.** Every proper unrooted binary phylogenetic network of level at most $4$ is tree-based, and binary networks of level greater than $4$ need not be tree-based.

**Proposition 3.** There are exactly two minimal (in the number of vertices) proper unrooted binary level-$5$ networks that are not tree-based. Both have exactly $12$ vertices, and every other proper unrooted binary level-$5$ network that is not tree-based has more than $12$ vertices. Both minimal networks have two leaves $x,y$ and are symmetric under swapping $x$ and $y$.

A previously published level-$5$ example of a non-tree-based binary network is in fact tree-based: it has a spanning path between its two leaves.

## Proof depends on

- [Level-3 bound for non-binary unrooted tree-based networks](level-3-bound-for-non-binary-unrooted-tree-based-networks.md)

## Expansion

Reducing to blobs with two leaves $x,y$, the leaf-connecting construction deletes the leaves and joins their attachment points, producing a cubic graph $G(N)$ with at most as many vertices as $N$; $N$ is tree-based exactly when $G(N)$ has a Hamiltonian cycle through the new edge. Handshaking forces even vertex counts, and the blob bound $|V(B)|\le2k$ limits the size of the cubic graphs to be examined at each level. The Appendix analyzes Hamiltonicity of these cubic graphs to give an alternative proof of the level-$4$ theorem and to identify the two minimal level-$5$ counterexamples with $12$ vertices.

## Sources

- Mareike Fischer, Michelle Galla, Lina Herbst, Yangjing Long and Kristina Wicke, "Unrooted non-binary tree-based phylogenetic networks", arXiv (2018), Section 2.2 (Proposition 1), Section 3.3 "Unrooted binary tree-based networks" (Theorem 2, Proposition 3) and the Appendix (alternative proof of the binary level-$4$ theorem and proof of Proposition 3), <https://doi.org/10.48550/arXiv.1810.06853> Published version: Discrete Applied Mathematics 294 (2021) 10–30, <https://doi.org/10.1016/j.dam.2021.01.005>.
