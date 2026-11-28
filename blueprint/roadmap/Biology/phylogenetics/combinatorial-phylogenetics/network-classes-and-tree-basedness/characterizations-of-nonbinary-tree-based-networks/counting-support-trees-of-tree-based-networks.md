# Counting support trees of tree-based networks

**Setting.** A rooted **phylogenetic network** on $X$ is a rooted acyclic digraph without parallel arcs whose root has out-degree at least one, whose vertices of out-degree zero are exactly $X$ (each of in-degree one), and whose other vertices are either *tree vertices* (in-degree one, out-degree at least two) or *reticulations* (in-degree at least two, out-degree one). An *omnian* is a non-leaf vertex all of whose children are reticulations. $N$ is **tree-based** if it is obtained from a phylogenetic $X$-tree $T$ (the base tree) by subdividing arcs and adding linking arcs between attachment points, or from a non-leaf vertex of $T$ to an attachment point; the subdivided $T$ is a *support tree*. Let $\mathrm{Sup}(N)$ be the set of support trees of a tree-based network $N$. An arc $(u,v)$ is *arboreal* if $u$ is a reticulation or $v$ is a tree vertex or leaf; arboreal arcs lie in every support tree. Let $R_t$ be the reticulations with no reticulation parent, $Q_t$ the vertices with a child in $R_t$, and $\mathcal J_N$ the bipartite graph on $Q_t\cup R_t$ with an edge for each arc from $Q_t$ to $R_t$. A *supporting set* is a set of edges of $\mathcal J_N$ meeting every omnian of $Q_t$ at least once and every reticulation of $R_t$ exactly once.

**Theorem.** A set $A'$ of arcs of a tree-based network $N$ is the arc set of a support tree if and only if $A'$ is the union of the arboreal arcs and a supporting set of $\mathcal J_N$. Hence $|\mathrm{Sup}(N)|$ equals the number of supporting sets of $\mathcal J_N$.

**Theorem (binary networks).** If $N$ is binary and tree-based, each component of $\mathcal J_N$ is a cycle, a path whose end vertices are non-omnian tree vertices, or a path with exactly one omnian end. Then

$$
|\mathrm{Sup}(N)|=2^{c}\prod_{P\in\pi(\mathcal J_N)}\tfrac12\bigl(v(P)+1\bigr),
$$

where $c$ is the number of cycle components of $\mathcal J_N$, $\pi(\mathcal J_N)$ is the set of path components without an omnian end and $v(P)$ is the number of vertices of $P$. Equivalently, in terms of the omnian–reticulation graph $\mathcal B_N$,

$$
|\mathrm{Sup}(N)|=2^{c}\prod_{P\in\pi(\mathcal B_N)}\tfrac12\bigl(v(P)+3\bigr),
$$

with $c$ the number of cycles of $\mathcal B_N$ and $\pi(\mathcal B_N)$ the path components with both ends reticulations, which shows that an earlier upper bound is an equality. The count is computable in polynomial time, although counting displayed trees is #P-complete even for temporal tree-based networks.

**Example.** The bread wheat network with three ancient hybridizations has $\mathcal J_N$ consisting of three disjoint three-vertex paths, so $|\mathrm{Sup}(N)|=2^0\cdot2^3=8$.

## Proof depends on

- [Path-partition characterizations of nonbinary tree-based networks](path-partition-characterizations-of-nonbinary-tree-based-networks.md)

## Expansion

A support tree needs exactly one incoming arc at every non-root vertex and at least one outgoing arc at every non-leaf vertex. Arboreal arcs are forced; the only freedom is which tree-vertex parent feeds each reticulation without a reticulation parent, subject to every omnian keeping a child, which is exactly a supporting set. In the binary case components are independent: a cycle has two alternating choices, a path between non-omnian ends has one choice per tree vertex (the vertex that takes both neighboring reticulations), and a path with an omnian end is forced.

## Sources

- Joan Carles Pons, Charles Semple and Mike Steel, "Tree-based networks: characterisations, metrics, and support trees", arXiv (2017), Section 4 "Embedded support trees" (the arboreal-arc theorem and its corollary, the component lemma, the counting theorem for $\mathcal J_N$, the component-correspondence lemma and the counting theorem for $\mathcal B_N$), <https://doi.org/10.48550/arXiv.1710.07836> Published version: Journal of Mathematical Biology 78 (2018) 899–918, <https://doi.org/10.1007/s00285-018-1296-9>.
