# Identifiability of level-1 networks from average distances

Let $d_N$ denote the tip-to-tip [average distances](average-distance-on-a-phylogenetic-network.md) of a semidirected network $N$ on $X$.

**Theorem (mixed representation, level 1).** Let $N_1, N_2$ be level-1 semidirected networks on $X$ with no $2$- or $3$-cycles, no degree-2 nodes, and internal tree edges of positive length. Let $N_i^*$ be the *mixed network representation* of the zipped-up version of $N_i$, in which each $4$-cycle is replaced by split (undirected) edges and all other tree and hybrid edges and identifiable edge parameters are kept. Then

$$d_{N_1} = d_{N_2} \implies N_1^* = N_2^*.$$

**Corollary.** If $N_1, N_2$ are zipped-up level-1 semidirected networks on $X$ with tree edges of positive length, without $2$-, $3$- or $4$-cycles and without degree-2 nodes, then $d_{N_1} = d_{N_2}$ implies $N_1 = N_2$.

**Theorem (non-identifiability beyond level 1).** For every $k \ge 2$ and $n \ge 4$, zipped-up binary semidirected networks of level at most $k$ on $n$ taxa with no $2$- or $3$-cycles are not generically identifiable from average distances: there are topologies $N_1 \ne N_2$ and parameter sets $\Omega_1, \Omega_2$ of positive Lebesgue measure such that every $(\ell_1,\gamma_1) \in \Omega_1$ has some $(\ell_2,\gamma_2) \in \Omega_2$ with $d_{(N_1,\ell_1,\gamma_1)} = d_{(N_2,\ell_2,\gamma_2)}$. The same holds within tree-child networks.

Information loss in level-1 networks is therefore localized at $4$-cycles, where the placement of the reticulation is unidentifiable, and at $3$-cycles, which can be swapped for a tree node with adjusted lengths.

## Depends on

- [Average distance on a phylogenetic network and its basic invariances](average-distance-on-a-phylogenetic-network.md)
- [The distance split tree refines the tree of blobs](distance-split-tree-refines-the-tree-of-blobs.md)

## Expansion

The distance split tree recovers the tree-like skeleton; within each level-1 blob (a cycle) the distances restricted to taxa around the cycle determine the hybrid node position and parameters when the cycle has at least $5$ sides, while for a $4$-cycle only a split-network summary is determined. The non-identifiability for level $\ge 2$ is shown on $4$ taxa and embedded in larger networks.

## Sources

- Jingcheng Xu and Cécile Ané, "Identifiability of local and global features of phylogenetic networks from average distances", Journal of Mathematical Biology (2022), <https://doi.org/10.1007/s00285-022-01847-8>. arXiv:2110.11814. Theorem 7, Theorem 12 and Corollary 13; Proposition 6.
