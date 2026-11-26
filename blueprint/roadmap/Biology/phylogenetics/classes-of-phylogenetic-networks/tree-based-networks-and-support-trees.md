# Tree-based networks and support trees

Let $N$ be a rooted binary phylogenetic network on $X$, as in [tree-child networks](tree-child-networks.md). $N$ is **tree-based** with base tree $T$, a rooted binary phylogenetic $X$-tree, if $N$ arises from $T$ by subdividing arcs of $T$ with *attachment points*, adding *linking arcs* between attachment points so that the graph stays binary and acyclic, and suppressing attachment points not incident to a linking arc.

**Proposition (support-tree characterization).** $N$ is tree-based if and only if it has a *support tree*: a rooted spanning tree of $N$ (all vertices, a subset of the arcs) whose leaf set is exactly $X$.

**Corollary.** Every tree-child network is tree-based. Indeed, deleting, for each reticulation, either one of its two incoming arcs yields a support tree.

## Depends on

- [Tree-child networks](tree-child-networks.md)

## Expansion

Given a support tree $S$, the arcs of $N$ outside $S$ join vertices of $S$ of in- and out-degree one in $S$; these are the attachment points and the deleted arcs are the linking arcs, and suppressing degree-two vertices of $S$ gives the base tree. Conversely, a base-tree construction keeps the subdivided arcs of $T$ as a spanning tree with leaves $X$. For the corollary, after deleting one incoming arc of every reticulation every non-root vertex has in-degree exactly one, so in an acyclic graph with a unique source the remaining arcs form a rooted spanning tree. No arc into a tree vertex or leaf was deleted, and in a tree-child network every non-leaf vertex has such a child, so no internal vertex becomes a leaf; the leaf set stays $X$. A tree-based network can have several base trees, and universal tree-based networks have every phylogenetic $X$-tree as a base tree.

## Sources

- S. Kong, J. C. Pons, L. Kubatko and K. Wicke, "Classes of explicit phylogenetic networks and their biological and mathematical significance", Journal of Mathematical Biology 84 (2022), 47, <https://doi.org/10.1007/s00285-022-01746-y>. Section 3.1, "Tree-based networks", and Table 1.
- A. R. Francis and M. Steel, "Which phylogenetic networks are merely trees with additional arcs?", Systematic Biology 64 (2015), 768–777, <https://doi.org/10.1093/sysbio/syv037>.
