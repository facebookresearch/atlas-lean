# Regular phylogenetic networks are terminal planar exactly when pyramidal

**Definitions.** For a rooted phylogenetic network $N$ on $X$, the cluster of a vertex $v$ is the set of leaves below $v$, and $\mathcal{C}(N)$ is the cluster system of $N$. For a cluster system $\mathcal{C}$ on $X$, $H(\mathcal{C})$ is its Hasse diagram (cover digraph) under inclusion, viewed as a network. $N$ is *regular* if $N \cong H(\mathcal{C}(N))$. A cluster system is a *prepyramid* if there is a bijection $f : X \to \{1, \dots, n\}$ mapping every cluster to an interval, and a *pyramid* if it is a prepyramid closed under (nonempty) intersection; $N$ is *pyramidal* if $\mathcal{C}(N)$ is a pyramid. $N$ is *terminal planar* if it has a planar drawing with the root and all leaves on the outer face.

**Theorem.** A regular phylogenetic network $N$ on $X$ is terminal planar if and only if $N$ is pyramidal. Consequently, terminal planarity of a regular network can be decided in $O(|X|^2)$ time.

## Proof sketch

If the clusters are intervals of a leaf order and closed under intersection, the Hasse diagram can be drawn with leaves on a horizontal line in that order and each cluster vertex above its interval, giving a planar drawing with root and leaves on the outer face. Conversely, a terminal planar drawing orders the leaves around the outer face; planarity forces every cluster to be an interval of this cyclic order (one that can be cut at the root), and regularity, which makes $N$ the Hasse diagram of its clusters, gives closure under intersection. The equivalence uses that the completion $N^*$ (all leaves joined to a new sink) is upward planar iff $N$ is terminal planar, and that a poset is upward planar with a single source and sink iff it has order dimension at most $2$.

## Depends on

- [Hierarchy of planarity classes for rooted phylogenetic networks](hierarchy-of-planarity-classes-for-rooted-phylogenetic-networks.md)

## Sources

- Vincent Moulton and Taoyang Wu, "Planar Rooted Phylogenetic Networks", *IEEE/ACM Transactions on Computational Biology and Bioinformatics* 20 (2023), 1289–1297, <https://doi.org/10.1109/tcbb.2022.3185670>. Preprint version: arXiv:2203.10156 (2022), Section 5, Theorem 5.1 and its corollary, <https://doi.org/10.48550/arXiv.2203.10156>.
