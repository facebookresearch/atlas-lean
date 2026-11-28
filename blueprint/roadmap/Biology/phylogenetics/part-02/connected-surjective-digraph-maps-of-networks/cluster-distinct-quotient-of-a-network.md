# Cluster-distinct quotient of a phylogenetic network

For an $X$-network $N=(V,A,r,X)$ the **cluster** of a vertex is $\mathrm{cl}(v)=\{x\in X: v\le x\}$, the set of taxa descended from $v$. $N$ is **(successively) cluster-distinct** if $\mathrm{cl}(a)\ne\mathrm{cl}(b)$ for every arc $(a,b)$. Successive vertices with equal clusters influence exactly the same extant taxa and are hard to distinguish from data.

**Algorithm Cluster-Distinct.** Repeatedly identify the endpoints of any arc $(u,v)$ with $\mathrm{cl}(u)=\mathrm{cl}(v)$ (recomputing on the quotient), until no such arc remains; call the result $\mathrm{ClDis}(N)=N/S_m$.

**Theorem.**

1. $\mathrm{ClDis}(N)$ is a successively cluster-distinct $X$-network; it is acyclic if $N$ is, and it does not depend on the order in which the identifications are performed.
2. The natural projection $\phi:N\to\mathrm{ClDis}(N)$ is a connected surjective digraph (CSD) map, so $\mathrm{ClDis}(N)$ has a wired lift into $N$.
3. The cluster function can be computed in time $O(|A|+|V|)$, and the algorithm runs in time $O(|A|)$.
4. (Universal property) If $f:N\to N'$ is any CSD map such that $f(u)=f(v)$ whenever $(u,v)\in A$ and $\mathrm{cl}(u,N)=\mathrm{cl}(v,N)$, then there is a unique CSD map $g:\mathrm{ClDis}(N)\to N'$ with $f=g\circ\phi$.

## Depends on

- [Wired lifts along connected surjective digraph maps of phylogenetic networks](wired-lifts-of-csd-maps.md)

## Expansion

Each identification merges the two endpoints of an arc, a connected set, so the projection is a composition of CSD maps and hence CSD. Clusters are preserved by identifying an arc whose endpoints have equal clusters (descendant sets of other vertices do not change), which is why the order of identifications is irrelevant: the final partition is the set of connected components of the subgraph formed by all arcs of $N$ with equal-cluster endpoints. Computing clusters by a reverse topological sweep and those components by a graph search gives the linear running time. The universal property is the factorization of a CSD map through a quotient by a finer connected partition.

## Sources

- Stephen J. Willson, "CSD Homomorphisms Between Phylogenetic Networks", arXiv (2010). Section 5 (Algorithm Cluster-Distinct, Theorem 5.1, Corollary 5.2, Theorems 5.3 and 5.4). <https://doi.org/10.48550/arXiv.1005.2108>. Published version: IEEE/ACM Transactions on Computational Biology and Bioinformatics 9(4) (2012), 1128–1138, <https://doi.org/10.1109/tcbb.2012.52>; locators above refer to the arXiv version.
