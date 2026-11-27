# Hamiltonian sufficient conditions for unrooted tree-basedness

**Setting.** An **unrooted phylogenetic network** on a finite set $X$ is a connected simple graph with no degree-two vertices whose degree-one vertices (leaves) are bijectively labelled by $X$; it is binary if every inner vertex has degree $3$. It is **tree-based** if it has a spanning tree whose leaf set is exactly $X$ (a support tree). A *blob* is a maximal connected subgraph without cut edges, and a network is **proper** if removing any cut edge or cut vertex leaves components that each contain a leaf. For a network $N$ with $|X|\ge2$, the *leaf cut graph* $\mathcal{LCUT}(N)$ deletes all labelled leaves and their edges; $N$ is **$\mathcal H$-connected** if it is proper and $\mathcal{LCUT}(N)$ is Hamilton connected (a Hamiltonian path joins every pair of vertices). The *leaf connecting* procedure first keeps only one leaf per attachment vertex, then repeatedly removes two leaves $x_1,x_2$ and joins their attachment points by a new edge (subdividing to avoid parallel edges), handling a last odd leaf similarly; $\mathcal{LCON}(N)$ is the set of simple graphs obtainable this way.

**Theorem.** Let $N$ be a proper unrooted phylogenetic network on $X$ with $|X|\ge2$. Then $N$ is tree-based in each of the following cases.

1. Two leaves $x,y$ have adjacent attachment points $u,v$, and some path in $N$ from $u$ to $v$ visits all inner vertices.
2. $N$ is $\mathcal H$-connected.
3. Some $G\in\mathcal{LCON}(N)$ has a Hamiltonian cycle using an edge of $G$ that is not in $N$ and did not arise from deleting the last leaf in the odd case.
4. Some $G\in\mathcal{LCON}(N)$ is Hamiltonian and at least two new vertices had to be added when connecting the attachment points of two leaves, to avoid parallel edges.

**Corollary.** If $\mathcal{LCUT}(N)$ is not Hamiltonian and some $G\in\mathcal{LCON}(N)$ is a $10$-tough chordal graph, then $N$ is tree-based (every $10$-tough chordal graph is Hamiltonian).

**Theorem ($\mathcal H$-connected edgebased networks).** If $N$ is $\mathcal H$-connected and edgebased, then $\mathcal{LCUT}(N)$ has fewer than four vertices; precisely, either $N$ is a tree with at most one inner edge, or $N$ has exactly one cycle, this cycle is a triangle and $\mathcal{LCUT}(N)$ is that triangle. In particular all such networks are chordal.

None of the sufficient conditions is necessary.

## Depends on

- [Edgebased networks and generalized series-parallel graphs](edgebased-networks-and-generalized-series-parallel-graphs.md)

## Expansion

A support tree with two leaves is a Hamiltonian path between their attachment points, and more leaves only relax the requirement, so Hamiltonian paths or cycles through the inner vertices that start and end at attachment points can be turned into support trees by hanging the remaining leaves off the path. A Hamiltonian cycle in a leaf-connected graph that uses a newly added edge opens, after deleting that edge, into a Hamiltonian path between two attachment points of the original network. For the last theorem, auxiliary lemmas show that the leaf cut graph of an $\mathcal H$-connected network has no cut edges, and combining this with edgebasedness bounds the leaf cut graph by three vertices; a connected graph on at most three vertices without cut edges is a vertex, an edge or a triangle.

## Sources

- Mareike Fischer, Michelle Galla, Lina Herbst, Yangjing Long and Kristina Wicke, "Classes of treebased networks", arXiv (2018), Section 3.1 "Reducing phylogenetic networks to related graphs" (leaf cutting, leaf shrinking, leaf connecting, $\mathcal H$-connected networks) and Section 3.2.2 "Other networks that are guaranteed to be treebased" (the four-part sufficiency theorem and the $10$-tough chordal corollary) and Section 3.2.3 "Relationships between different classes of treebased networks", <https://doi.org/10.48550/arXiv.1810.06844> Published version: Visual Computing for Industry, Biomedicine, and Art 3 (2020) 12, <https://doi.org/10.1186/s42492-020-00043-z>.
