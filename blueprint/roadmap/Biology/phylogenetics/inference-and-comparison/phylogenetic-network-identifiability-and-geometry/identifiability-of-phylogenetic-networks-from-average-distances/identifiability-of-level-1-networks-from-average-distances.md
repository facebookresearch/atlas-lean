# Identifiability of level-1 networks from average distances

Let $d_N$ denote the tip-to-tip [average distances](average-distance-on-a-phylogenetic-network.md) of a semidirected network $N$ on $X$, with edge lengths $\ell \ge 0$ and hybridization parameters $\gamma \in (0,1)$ on hybrid edges ($\gamma = 1$ on tree edges).

**Theorem (mixed representation, level 1).** Let $N_1, N_2$ be level-1 semidirected networks on $X$ with no $2$- or $3$-cycles, no degree-2 nodes, and internal tree edges of positive length. Let $N_i^*$ be the *mixed network representation* (Definition 17) of the zipped-up version of $N_i$ (Definition 9, as on the average-distance page). It is built in two steps. First, in each $4$-cycle, with tips $a, g, b, h$ chosen below its four nodes in circular order, the cycle is replaced by a *split blob*: its four edges become undirected split edges with $\gamma = 1$, the two pairs of opposite edges forming two classes whose lengths are the canonical split weights $\hat t_{hb \mid ga} = \tfrac12(d_{gh} + d_{ab} - d_{ga} - d_{hb})$ and $\hat t_{ha \mid gb} = \tfrac12(d_{gh} + d_{ab} - d_{gb} - d_{ha})$ (Definition 15), and tree edges are inserted between the cycle nodes and their outside edges, with the lengths of these adjacent tree edges adjusted so that tip-to-tip distances are preserved (Fig. 17; in a zipped-up network the edge at the former hybrid node is not needed). Second, degree-2 nodes are suppressed. All other tree edges, hybrid edges, lengths and hybridization parameters are kept, and average distances on $N_i^*$ are computed over mixed up-down paths (Definition 18), so that $d_{N_i^*} = d_{N_i}$ on tips (Theorem 26). Then

$$d_{N_1} = d_{N_2} \implies N_1^* = N_2^*.$$

**Corollary.** If $N_1, N_2$ are zipped-up level-1 semidirected networks on $X$ with tree edges of positive length, without $2$-, $3$- or $4$-cycles and without degree-2 nodes, then $d_{N_1} = d_{N_2}$ implies $N_1 = N_2$.

**Theorem (non-identifiability beyond level 1).** For every $k \ge 2$ and $n \ge 4$, zipped-up binary semidirected networks of level at most $k$ on $n$ taxa with no $2$- or $3$-cycles are not generically identifiable from average distances: there are topologies $N_1 \ne N_2$ and parameter sets $\Omega_1, \Omega_2$ of positive Lebesgue measure such that every $(\ell_1,\gamma_1) \in \Omega_1$ has some $(\ell_2,\gamma_2) \in \Omega_2$ with $d_{(N_1,\ell_1,\gamma_1)} = d_{(N_2,\ell_2,\gamma_2)}$. The same holds within tree-child networks.

Information loss in level-1 networks is therefore localized at $4$-cycles, where the placement of the reticulation is unidentifiable, and at $3$-cycles, which can be swapped for a tree node with adjusted lengths.

## Depends on

- [Average distance on a phylogenetic network and its basic invariances](average-distance-on-a-phylogenetic-network.md)

## Proof depends on

- [The distance split tree refines the tree of blobs](distance-split-tree-refines-the-tree-of-blobs.md)

## Expansion

The distance split tree recovers the tree-like skeleton; within each level-1 blob (a cycle) the distances restricted to taxa around the cycle determine the hybrid node position and parameters when the cycle has at least $5$ sides, while for a $4$-cycle only a split-network summary is determined. The non-identifiability for level $\ge 2$ is shown on $4$ taxa and embedded in larger networks.

## Sources

- Jingcheng Xu and Cécile Ané, "Identifiability of local and global features of phylogenetic networks from average distances", Journal of Mathematical Biology (2022), <https://doi.org/10.1007/s00285-022-01847-8>. arXiv:2110.11814. Definitions 9 and 15–18; Theorem 7, Theorem 12 and Corollary 13; Theorem 26; Proposition 6.
