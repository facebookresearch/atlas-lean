# Fully tree-based nonbinary unrooted networks and their colourability

**Setting.** Use the three notions of tree-basedness (loose, usual, strict) for unrooted nonbinary networks on leaf set $X$ from [Three notions of tree-basedness for nonbinary unrooted networks](three-notions-of-tree-basedness-for-nonbinary-unrooted-networks.md). An *embedded tree* of $N$ is a subtree with leaf set $X$; $N$ is *loosefully*, *fully* or *strictfully* tree-based if every embedded tree is a base tree in the loose, usual or strict sense. A network is *simple* if all its cut-edges are pendant. A *cut-vertex* is a vertex whose deletion disconnects $N$; its *cut-components* are the resulting components.

**Theorem.** Let $N$ be a simple network on $X$.

1. $N$ is strictfully tree-based if and only if $N$ is a binary level-$1$ network or a star tree.
2. $N$ is loosefully tree-based if and only if every non-leaf vertex is a cut-vertex.
3. $N$ is fully tree-based if and only if (a) every non-leaf vertex either has degree $3$ and a pendant edge, or is a cut-vertex with at least $3$ cut-components, and (b) every vertex of degree at least $4$ is adjacent only to vertices of degree $3$ or $1$.

Colourability:

4. Every tree-based network is $4$-colourable, while for every $k$ there are loosely tree-based networks with chromatic number at least $k$.
5. Every strictly tree-based network is $3$-colourable, and chromatic number $3$ is attained.

Since chromatic number is easy to bound from below, these results give a quick certificate that a network is not tree-based (chromatic number at least $5$) or not strictly tree-based (at least $4$).

## Expansion

For the full classifications one checks which local configurations allow an embedded tree that violates the base-tree conditions: a vertex that is not a cut-vertex lies on a cycle and can be avoided by some embedded tree, or left as an unsuppressible vertex, which breaks loose base-tree status. The degree conditions in part 3 prevent embedded trees from omitting an edge between two vertices of degree at least $4$ or leaving degree-$2$ vertices that had degree above $3$. For colouring, a strictly tree-based network is a subdivided tree with extra edges joining degree-$3$ attachment points; two-colouring the tree and recolouring the attachment points greedily, each having only three neighbours, gives three colours. Allowing edges to original vertices, as in tree-based networks, costs at most one more colour, whereas loose tree-basedness only requires a Hamiltonian-path-like spanning tree, compatible with arbitrarily dense added edges and hence large cliques.

## Depends on

- [Three notions of tree-basedness for nonbinary unrooted networks](three-notions-of-tree-basedness-for-nonbinary-unrooted-networks.md)

## Sources

- Michael Hendriksen, "Tree-Based Unrooted Nonbinary Phylogenetic Networks", arXiv:1711.04935 (2017): Section 4 (definitions of strictfully, fully and loosefully tree-based networks; the three classification theorems), Section 5 (the colourability theorems for tree-based and strictly tree-based networks). <https://doi.org/10.48550/arXiv.1711.04935> Published version: Mathematical Biosciences 302 (2018) 131–138, <https://doi.org/10.1016/j.mbs.2018.06.005>.
