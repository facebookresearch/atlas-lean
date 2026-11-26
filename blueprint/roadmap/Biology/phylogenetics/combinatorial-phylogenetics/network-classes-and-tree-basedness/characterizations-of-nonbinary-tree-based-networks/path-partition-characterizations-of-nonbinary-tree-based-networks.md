# Path-partition characterizations of nonbinary tree-based networks

**Setting.** A rooted **phylogenetic network** on $X$ is a rooted acyclic digraph without parallel arcs whose root has out-degree at least one, whose vertices of out-degree zero are exactly $X$ (each of in-degree one), and whose other vertices are either *tree vertices* (in-degree one, out-degree at least two) or *reticulations* (in-degree at least two, out-degree one). An *omnian* is a non-leaf vertex all of whose children are reticulations. $N$ is **tree-based** if it is obtained from a phylogenetic $X$-tree $T$ (the base tree) by subdividing arcs and adding linking arcs between attachment points, or from a non-leaf vertex of $T$ to an attachment point; the subdivided $T$ is a *support tree*. For a digraph $D=(V,A)$ let $\mathcal G_D$ be its bipartite representation, with two copies $V_1,V_2$ of $V$ and an edge $\{u,v\}$ for each arc $(u,v)\in A$. Let $\mathcal B_N$ be the bipartite graph on omnians $O$ and reticulations $R$ with an edge for each arc from an omnian to a reticulation. $N$ is *temporal* if some $\lambda:V\to\mathbb R$ increases strictly along tree arcs and is constant along reticulation arcs. $N$ has the *antichain-to-leaf property* if every antichain of $k$ vertices is joined to leaves by $k$ vertex-disjoint paths.

**Lemma.** $N$ is tree-based if and only if some binary refinement of $N$ is tree-based, if and only if $N$ has a rooted spanning tree with the same root whose leaves all lie in $X$. (A tree-based network may also have binary refinements that are not tree-based.)

**Theorem (omnian matchings).** $N$ is tree-based if and only if $\mathcal B_N$ has a matching of size $|O|$. If $\mathcal B_N$ has no maximal path starting and ending at omnians then $N$ is tree-based, and for binary $N$ this is equivalent. The binary characterization by matchings that cover all reticulations in the tree-vertex/reticulation graph does not extend to nonbinary networks.

**Theorem (path partitions).** For a phylogenetic network $N=(V,A)$ on $X$ the following are equivalent:

1. $N$ is tree-based;
2. $N$ has an antichain $A'\subseteq V$ and a partition of $V$ into $|A'|$ chains, each forming a path of $N$ that ends at a leaf;
3. for every $U\subseteq V$ there are vertex-disjoint paths ending at leaves such that each element of $U$ lies on exactly one of them;
4. $V$ can be partitioned into vertex-disjoint paths each ending at a leaf;
5. $\mathcal G_N$ has a matching of size $|V|-|X|$.

**Theorem (temporal networks).** A temporal phylogenetic network is tree-based if and only if it satisfies the antichain-to-leaf property. For general networks this property is necessary but not sufficient.

## Expansion

A support tree assigns to each non-leaf vertex one outgoing tree arc to follow, so following these arcs partitions $V$ into paths ending at leaves; conversely such a path partition, with each path's first vertex attached by its incoming arc, is a spanning tree with leaves in $X$. A matching in $\mathcal G_N$ picks for each vertex at most one successor and one predecessor, and has size $|V|-|X|$ exactly when every non-leaf vertex has a successor, i.e. a path partition. For temporal networks the proof inducts on vertices: children of the root are tree vertices, the earliest layer is contracted into the root, and Hall's theorem applied to omnians in that layer extends a support tree of the contracted network. Nonbinary temporal networks need not have temporal binary refinements, so the binary result cannot be invoked directly.

## Sources

- Joan Carles Pons, Charles Semple and Mike Steel, "Tree-based networks: characterisations, metrics, and support trees", arXiv (2017), Section 2.1 "Tree-based networks" (the equivalence lemma) and Section 3 "Characterisations and metrics", subsections "Bipartite graphs and tree-based characterisations", "Generalising tree-based characterisations" and "Characterising temporal tree-based networks", <https://doi.org/10.48550/arXiv.1710.07836> Published version: Journal of Mathematical Biology 78 (2018) 899–918, <https://doi.org/10.1007/s00285-018-1296-9>.
