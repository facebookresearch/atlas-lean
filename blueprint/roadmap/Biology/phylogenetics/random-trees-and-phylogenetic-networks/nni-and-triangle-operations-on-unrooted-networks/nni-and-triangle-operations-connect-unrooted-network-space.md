# NNI and triangle operations connect the space of unrooted phylogenetic networks

**Setting.** Let $X$ be a set of at least three taxa. An *(unrooted phylogenetic) network on $X$* is a connected graph whose degree-1 vertices are exactly the elements of $X$ and whose other vertices all have degree 3 (a connected 1–3 graph with leaf set $X$); phylogenetic trees on $X$ are the networks without cycles. A *blob* is a maximal bridgeless connected subgraph, and a network is *level-$k$* if deleting at most $k$ edges from each blob yields a tree.

**Operations.**
- *NNI.* Given a path $v_1,v_2,v_3,v_4$ in a network $N$ such that neither $\{v_1,v_3\}$ nor $\{v_2,v_4\}$ is an edge, replace it by the path $v_1,v_3,v_2,v_4$, keeping all other edges. On trees this is the classical nearest-neighbour interchange; it preserves the number of vertices and is reversible.
- *Triangle operations.* $\Delta^+$ inserts a length-3 cycle (a triangle) into a network so that the result is again a network, and $\Delta^-$ removes an isolated triangle (one sharing no edge with another triangle); they are mutually inverse and change the number of vertices by $\pm2$.

**Theorem (construction).** A graph $N$ with $X$ among its vertices is a network on $X$ if and only if it can be obtained from some phylogenetic tree on $X$ by a finite sequence of NNI and $\Delta^+$ operations.

**Theorem (generators).** For $k\ge2$, a multigraph is a level-$k$ generator (a bridgeless cubic multigraph with $2(k-1)$ vertices) if and only if it arises from the theta graph (two vertices joined by three parallel edges) by $k-2$ applications of two local expansion operations.

**Theorem (NNI connectivity).** If $N$ and $N'$ are networks on $X$ with the same number of vertices, then $N$ can be transformed into $N'$ by a finite sequence of NNI operations.

**Theorem (full connectivity).** Any two networks on $X$ are connected by a finite sequence of NNI and $\Delta^{\pm}$ operations.

**Corollary (network-space metrics).** Let $\mathcal N(X)$ be the set of networks on $X$ and $\mathcal N_i(X)$ those with a given number of vertices. The minimal number $d(N,N')$ of NNI and triangle operations transforming $N$ into $N'$ is a metric on $\mathcal N(X)$, and the minimal number $d_{\mathrm{NNI}}(N,N')$ of NNI operations is a metric on each $\mathcal N_i(X)$.

These results generalize the classical fact that NNI moves connect all binary phylogenetic trees on $X$, and they define a "network space" in which tree space is the stratum of networks with $2|X|-2$ vertices.

## Expansion

The proofs pass through cubic graph theory. Each blob of a network, after suppressing degree-2 vertices, is a generator, and generators are built from the theta graph by local expansions, so every network is a tree with generators "hung" on it. NNI moves can relocate leaves and pendant subtrees across a blob and can realize the local expansions, which reduces connectivity to transforming one canonical network with a given vertex count into another; the triangle operations then move between vertex counts. Symmetry and reversibility of both operations give the metric axioms.

## Sources

- Katharina T. Huber, Vincent Moulton, Taoyang Wu, "Transforming phylogenetic networks: Moving beyond tree space", Journal of Theoretical Biology 404 (2016), 30–39, <https://doi.org/10.1016/j.jtbi.2016.05.030>. Published version of arXiv:1601.01788, cited next; locators there refer to the arXiv version.
- Katharina T. Huber, Vincent Moulton, Taoyang Wu, "Transforming phylogenetic networks: Moving beyond tree space", arXiv:1601.01788 (2016): Section 2 (definitions), Theorem 1 (construction), Theorem 2 (generators), Theorem 3 (NNI connectivity), Theorem 4 (NNI and triangle operations), Theorem 5 (metrics). <https://doi.org/10.48550/arXiv.1601.01788>
