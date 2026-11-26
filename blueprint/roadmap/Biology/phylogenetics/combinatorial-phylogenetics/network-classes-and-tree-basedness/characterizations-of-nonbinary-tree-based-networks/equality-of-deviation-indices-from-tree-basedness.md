# Equality of deviation indices from tree-basedness

**Setting.** A rooted **phylogenetic network** on $X$ is a rooted acyclic digraph without parallel arcs whose root has out-degree at least one, whose vertices of out-degree zero are exactly $X$ (each of in-degree one), and whose other vertices are either *tree vertices* (in-degree one, out-degree at least two) or *reticulations* (in-degree at least two, out-degree one). An *omnian* is a non-leaf vertex all of whose children are reticulations. $N$ is **tree-based** if it is obtained from a phylogenetic $X$-tree $T$ (the base tree) by subdividing arcs and adding linking arcs between attachment points, or from a non-leaf vertex of $T$ to an attachment point; the subdivided $T$ is a *support tree*. Attaching a new leaf subdivides an arc $(u,v)$ by a new vertex $w$ and adds an arc from $w$ to a new leaf. For $N=(V,A)$ define:

- $l(N)$: the minimum number of leaves outside $X$ in a rooted spanning tree of $N$;
- $p(N)=d(N)-|X|$, where $d(N)$ is the minimum number of vertex-disjoint paths partitioning $V$;
- $t(N)$: the minimum number of new leaves that must be attached to make $N$ tree-based.

Each index is a well-defined nonnegative integer that vanishes exactly when $N$ is tree-based.

**Theorem.** For every (not necessarily binary) phylogenetic network $N$ on $X$,

$$
l(N)=p(N)=t(N)=(|V|-|X|)-m(\mathcal G_N)=|O|-m(\mathcal B_N),
$$

where $\mathcal G_N$ is the bipartite representation of $N$, $\mathcal B_N$ is the omnian–reticulation bipartite graph, $O$ is the set of omnians and $m(\cdot)$ is the size of a maximum matching. In particular all three distances to tree-basedness are computable in polynomial time.

## Proof depends on

- [Path-partition characterizations of nonbinary tree-based networks](path-partition-characterizations-of-nonbinary-tree-based-networks.md)

## Expansion

A maximum matching of $\mathcal G_N$ of size $m$ leaves $|V|-|X|-m$ non-leaf vertices without a successor, giving a path partition with that many extra paths and a spanning tree with that many extra leaves; attaching one new leaf at each such vertex makes the network tree-based. For the omnian form, attaching a leaf on an arc out of an unmatched omnian removes that omnian from $\mathcal B_N$ without changing the matching, so $t(N)\le|O|-m(\mathcal B_N)$ by induction; conversely each attachment reduces the number of omnians by at most one while a maximum matching can only grow, giving the reverse inequality.

## Sources

- Joan Carles Pons, Charles Semple and Mike Steel, "Tree-based networks: characterisations, metrics, and support trees", arXiv (2017), Section 3, subsection "Deviation measures" (the two theorems expressing $l(N)=p(N)=t(N)$ through maximum matchings of $\mathcal G_N$ and $\mathcal B_N$), <https://doi.org/10.48550/arXiv.1710.07836> Published version: Journal of Mathematical Biology 78 (2018) 899–918, <https://doi.org/10.1007/s00285-018-1296-9>.
