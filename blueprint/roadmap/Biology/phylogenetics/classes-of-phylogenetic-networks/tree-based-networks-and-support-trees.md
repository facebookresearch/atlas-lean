# Tree-based networks and support trees

Let $N$ be a rooted binary phylogenetic network on $X$, as in [tree-child networks](tree-child-networks.md). $N$ is **tree-based** with base tree $T$, a rooted binary phylogenetic $X$-tree, if $N$ arises as follows. Plant $T$ by adding a *stem*: a new vertex $\rho$ and an arc from $\rho$ to the root of $T$. Subdivide arcs of the planted tree, the stem included, with *attachment points*; add *linking arcs* between attachment points so that the graph stays binary, acyclic and without parallel arcs; suppress attachment points not incident to a linking arc; finally delete $\rho$ and its arc. The new root is the top attachment point of the stem if one remains (it is the tail of a linking arc, since an arc into it would close a cycle) and the root of $T$ otherwise. The stem lets a linking arc start at the root of $N$. This corrects the definition as printed in Kong et al., Section 3.1, which obtains $N$ from $T$ by three steps, "(i) Subdivide the arcs of T … (ii) Add arcs, so-called linking arcs, between pairs of attachment points, so that N remains binary and acyclic. (iii) Suppress every attachment point that is not incident to a linking arc", with no stem, and then states the support-tree characterization below as equivalent. Without the stem no linking arc can start at the root of $N$, since the root of $T$ is not an attachment point; the network in the Expansion has a support tree, but only one that leaves out the arc $r \to h$ from its root, so it does not arise from the three steps.

**Proposition (support-tree characterization).** $N$ is tree-based if and only if it has a *support tree*: a rooted spanning tree of $N$ (all vertices, a subset of the arcs) whose leaf set is exactly $X$.

**Corollary.** Every tree-child network is tree-based. Indeed, deleting, for each reticulation, either one of its two incoming arcs yields a support tree.

## Depends on

- [Tree-child networks](tree-child-networks.md)

## Expansion

Given a support tree $S$, every arc of $N$ outside $S$ joins two vertices of in-degree and out-degree one in $S$, except that its tail may be the root of $N$, which then has out-degree one in $S$. These vertices are the attachment points (the root of $N$ playing the role of the top attachment point of the stem, after a new $\rho$ is added above it) and the arcs outside $S$ are the linking arcs; suppressing the vertices of in-degree and out-degree one in $S$ gives the base tree. The root case occurs: in the network with arcs $r \to t, h$; $t \to q, p$; $q \to a, p$; $p \to h$; $h \to b$ on $X = \{a, b\}$, a support tree must keep $p \to h$, or $p$ becomes an extra leaf, so it omits $r \to h$. Conversely, a base-tree construction keeps the subdivided arcs of the planted $T$, without $\rho$ and its arc, as a spanning tree with leaves $X$. For the corollary, after deleting one incoming arc of every reticulation every non-root vertex has in-degree exactly one, so in an acyclic graph with a unique source the remaining arcs form a rooted spanning tree. No arc into a tree vertex or leaf was deleted, and in a tree-child network every non-leaf vertex has such a child, so no internal vertex becomes a leaf; the leaf set stays $X$. A tree-based network can have several base trees, and universal tree-based networks have every phylogenetic $X$-tree as a base tree.

## Sources

- S. Kong, J. C. Pons, L. Kubatko and K. Wicke, "Classes of explicit phylogenetic networks and their biological and mathematical significance", Journal of Mathematical Biology 84 (2022), 47, <https://doi.org/10.1007/s00285-022-01746-y>. Section 3.1, "Tree-based networks", and Table 1.
- A. R. Francis and M. Steel, "Which phylogenetic networks are merely trees with additional arcs?", Systematic Biology 64 (2015), 768–777, <https://doi.org/10.1093/sysbio/syv037>.
