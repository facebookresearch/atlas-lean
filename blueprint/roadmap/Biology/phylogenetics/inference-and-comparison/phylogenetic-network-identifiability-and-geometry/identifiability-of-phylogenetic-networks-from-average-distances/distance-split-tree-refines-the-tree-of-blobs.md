# The distance split tree refines the tree of blobs

Let $N$ be a semidirected phylogenetic network on $X$ with [average distances](average-distance-on-a-phylogenetic-network.md) $d_N$ and tree of blobs $\mathrm{BT}(N)$ (blobs are the subgraphs whose underlying undirected graphs are the 2-edge-connected components; the level of a blob $B$ is $|E_B| - |V_B| + 1$).

*Distance split tree* (Definitions 11–12). For a metric $d$ on $X$, a quartet $xy \mid uv$ satisfies the *4-point condition* if $d(x,y) + d(u,v) \le d(x,u) + d(y,v) = d(x,v) + d(y,u)$, and a split $A \mid B$ of $X$ satisfies it if every quartet $xy \mid uv$ with $x, y \in A$, $u, v \in B$ does. Let $\Sigma(d)$ be the set of splits satisfying the 4-point condition and $\Sigma'(d) \subseteq \Sigma(d)$ the splits that are compatible with every split in $\Sigma(d)$. The splits in $\Sigma'(d)$ are pairwise compatible, and the distance split tree $T_d$ is the unique $X$-tree whose splits are $\Sigma'(d)$. Keeping only $\Sigma'(d)$ matters: for a star tree of blobs, $\Sigma(d)$ may contain incompatible resolutions, none of which is a split of $\mathrm{BT}(N)$.

**Theorem (identifying the tree of blobs).** If $N$ has no blob of degree $2$ and no internal cut edge of length $0$, then the distance split tree $T_{d_N}$ of the tip-to-tip average distances is a refinement of $\mathrm{BT}(N)$ (contracting edges of $T_{d_N}$ yields $\mathrm{BT}(N)$).

**Theorem (level-1 networks).** Let $N$ be level-1, with internal tree edges of positive length and no blob of degree $2$. For each non-trivial blob $B$ and each node $u \in B$ with $k \ge 2$ incident edges $a_1u,\dots,a_ku$ outside $B$, refine $u$ by adding a new node $u'$, a tree edge $uu'$ of length $0$, and replacing each $a_iu$ by $a_iu'$; call the result $N^R$. Then the distance split tree of $N$ equals the tree of blobs of $N^R$.

The refinement cannot in general be avoided: there are level-2 networks whose tree of blobs is a star but whose average distances coincide with those of a resolved tree. Blobs of degree $2$ or $3$ can always be shrunk to a node, with adjusted cut-edge lengths, without changing average distances, so they are invisible to $d_N$.

## Depends on

- [Average distance on a phylogenetic network and its basic invariances](average-distance-on-a-phylogenetic-network.md)

## Expansion

A cut edge $e$ of $N$ splits $X$ into two sides, and every up-down path between the sides crosses it, so $d(a,u) = d(a,c) + \ell(e) + d(w,u)$ for tips $a$, $u$ on opposite sides of $e = cw$; hence every split of $\mathrm{BT}(N)$ satisfies the 4-point condition, strictly when $\ell(e) > 0$. If internal cut edges have positive length, a split satisfying the 4-point condition is compatible with every split of $\mathrm{BT}(N)$ (Lemma 17), so the splits of $\mathrm{BT}(N)$ lie in $\Sigma'(d_N)$. Splits of $N^R$ through a new edge $uu'$ of length $0$ are also distance splits, which is why the level-1 distance split tree resolves polytomies adjacent to blobs.

## Sources

- Jingcheng Xu and Cécile Ané, "Identifiability of local and global features of phylogenetic networks from average distances", Journal of Mathematical Biology (2022), <https://doi.org/10.1007/s00285-022-01847-8>. arXiv:2110.11814. Definitions 4, 11 and 12; Lemma 17; Proposition 4; Theorems 8 and 10; Example 1.
