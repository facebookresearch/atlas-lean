# Network quartet distance and the grove of displayed trees

**Setting.** Let $X$ be a taxon set with $|X| = n \ge 4$. For an unrooted binary tree $T$ on $X$ and distinct $x, y \in X$, let $\rho_{xy}(q) = 1$ if the quartet $q$ displayed by $T$ separates $x$ from $y$ (i.e. $q = xz|yw$) and $0$ otherwise, and define the tree quartet distance

$$d_T(x, y) = 2\sum_{\{z, w\} \subseteq X \setminus \{x, y\}} \rho_{xy}(T_{xyzw}) + 2n - 4, \qquad d_T(x, x) = 0.$$

Let $N^-$ be an unrooted level-1 network on $X$ (hybrid edges keep their direction) with exactly $k$ cycles of size at least $4$, and let the **grove** $\mathcal G(N^-)$ be the $2^k$ displayed trees obtained by deleting one hybrid edge in each such cycle (the choice of hybrid edge in a 2- or 3-cycle does not change the unrooted displayed tree). For an induced quartet network $Q_{xyzw}$, after contracting 2- and 3-cycles, set $\rho_{xy}(Q_{xyzw}) = 0$ if it is the tree $xy|zw$, $1/2$ if it has a 4-cycle in which $x, y$ are adjacent, and $1$ otherwise. The **network quartet distance** is

$$d_{Q,N^-}(x, y) = 2\sum_{\{z, w\} \subseteq X \setminus \{x, y\}} \rho_{xy}(Q_{xyzw}) + 2n - 4.$$

**Theorem.** For distinct $x, y \in X$,

$$\sum_{T \in \mathcal G(N^-)} d_T(x, y) = 2^k\, d_{Q,N^-}(x, y).$$

Moreover the left side is the split distance of the weighted split system $\omega_{N^-} = \sum_{T \in \mathcal G(N^-)} w_T$ (with $w_T$ the quartet weighting of $T$), whose support is the split set of $N^-$; this split system is circular, so $d_{Q,N^-}$ is a circular distance and can be fed to NeighborNet.

## Expansion

Fix $x, y, z, w$. If $\rho_{xy}(Q_{xyzw}) = 0$, no displayed tree separates $x, y$ on these four taxa. If it is $1/2$, the induced 4-cycle comes from two hybrid edges of $N^-$, each deleted in exactly half of the grove, so $2^{k-1}$ trees separate $x$ and $y$. If it is $1$, every tree in the grove separates them. Summing over $\{z, w\}$ and over the grove, and adding $2^k(2n - 4)$, gives the identity. Circularity comes from the fact that splits of trees displayed on an undirected level-1 network form a circular system.

## Depends on

- [Gene tree displaying a quartet split](../multispecies-coalescent/displays-split.md)
- [Buneman split index and split weights of a tree metric](../../phylogenetics/neighbor-joining/buneman-split-index-and-split-weights-of-a-tree.md)

## Proof depends on

- [Gene tree displaying a quartet split](../multispecies-coalescent/displays-split.md)
- [Split decomposition of a tree metric](../../phylogenetics/neighbor-joining/dist-eq-sum-darts.md)

## Sources

- E. S. Allman, H. Baños and J. A. Rhodes, "NANUQ: a method for inferring species networks from gene trees under the coalescent model", *Algorithms for Molecular Biology* 14 (2019), 24, <https://doi.org/10.1186/s13015-019-0159-2> (PMC6896299). Theorem 17 (tree case, from earlier work), Definitions 18, 20 and 22, Lemmas 19 and 21, Theorem 23, Corollaries 16 and 24.
