# Three notions of tree-basedness for nonbinary unrooted networks

**Setting.** An unrooted phylogenetic network on a finite leaf set $X$ is a connected graph with no degree-$2$ vertices whose degree-$1$ vertices are exactly $X$; a phylogenetic tree is a network that is a tree. *Subdividing* an edge inserts a new degree-$2$ vertex (an *attachment point*). A *blob* is a maximal connected subgraph without cut-edges. In the nonbinary setting, edges added to a base tree may join two attachment points, an attachment point and an original tree vertex, or two original vertices, which leads to three notions. A network $N$ on $X$ is

1. *loosely tree-based* if it has a spanning tree whose leaf set is exactly $X$;
2. *tree-based* if it has a spanning tree $T$ with leaf set $X$ that contains every edge between two vertices of degree at least $4$ and whose degree-$2$ vertices all had degree $3$ in $N$;
3. *strictly tree-based* if it has a spanning tree with leaf set $X$ that contains every edge incident to a vertex of degree at least $4$.

Strictly tree-based implies tree-based, which implies loosely tree-based.

**Theorem.**

1. $N$ is tree-based if and only if it arises from a phylogenetic tree $T$ on $X$ by subdividing edges and adding edges between attachment points or between an attachment point and an original vertex of $T$, so that every attachment point ends with degree $3$.
2. $N$ is strictly tree-based if and only if it arises from a tree $T$ by subdividing edges and adding edges only between attachment points, each attachment point ending with degree $3$.
3. $N$ is loosely, normally or strictly tree-based if and only if each of its blobs, with its pendant structure, is respectively loosely, normally or strictly tree-based.
4. The inclusions are strict, and some strictly nonbinary networks of level $5$ are not even loosely tree-based: a network on two leaves is loosely tree-based only if it has a Hamiltonian path between them.

For binary networks all three notions coincide with the tree-basedness of Francis, Huber and Moulton.

## Expansion

Given a spanning tree $T$ with the stated properties, the edges of $N$ outside $T$ are exactly the added edges; suppressing the degree-$2$ vertices of $T$ recovers a phylogenetic tree whose subdivision points are the endpoints of added edges. The degree conditions record which endpoints may be original vertices: in a strictly tree-based network every added edge has both ends at new attachment points, while in a tree-based network one end may be an original vertex of degree at least $3$, which then has degree at least $4$ in $N$. Conversely, building $N$ from a tree in this way leaves the subdivided tree as a spanning tree with the required properties. The blob decomposition works because spanning trees of $N$ restrict to spanning trees of each blob and can be glued along cut-edges.

## Sources

- Michael Hendriksen, "Tree-Based Unrooted Nonbinary Phylogenetic Networks", arXiv:1711.04935 (2017): Section 2 (networks, subdivision, cut-edges, blobs), Section 3 (definition of loosely, tree-based and strictly tree-based networks; the two construction theorems; the level-5 example that is not loosely tree-based; the blob proposition). <https://doi.org/10.48550/arXiv.1711.04935> Published version: Mathematical Biosciences 302 (2018) 131–138, <https://doi.org/10.1016/j.mbs.2018.06.005>.
