# BHV connection spaces linking tree spaces with different numbers of taxa

Let $\mathrm{BHV}_n$ be the Billera-Holmes-Vogtmann space of unrooted phylogenetic trees with $n$ labelled leaves and nonnegative internal edge weights: one nonnegative orthant of dimension $n-3$ per binary tree topology, glued along faces where edge weights vanish, with the induced intrinsic geodesic metric (a CAT(0) space).

Fix an unweighted binary *start tree* $T_s$ with $n$ leaves and a *connection step* $\ell\ge1$. The **BHV connection cluster** $C_{T_s,n,\ell}$ is the set of binary trees on $n+\ell$ leaves obtained from $T_s$ by attaching $\ell$ new labelled leaves to arbitrary edges (including leaf edges and edges created by earlier attachments). The **BHV connection space** $S_{T_s,n,\ell}\subseteq\mathrm{BHV}_{n+\ell}$ is the union of the $(n+\ell-3)$-dimensional orthants of the trees in $C_{T_s,n,\ell}$ together with their faces. Its **connection graph** $G_{T_s,n,\ell}$ has one vertex per split occurring in a tree of the cluster (one per one-dimensional orthant), with two vertices adjacent when the splits are compatible.

**Theorem.**

1. $|C_{T_s,n,\ell}| = \dfrac{(2(n+\ell)-5)!!}{(2n-5)!!}$.
2. $G_{T_s,n,\ell}$ has exactly $2^{\ell}(2n-2)-\ell-n-1$ vertices, i.e. the trees of $C_{T_s,n,\ell}$ contain exactly that many distinct nontrivial splits. Ren et al. (Theorem 2.2) print this number as the dimension of $S_{T_s,n,\ell}$; this page states it as a vertex count instead, because by the definition above $S_{T_s,n,\ell}$ is a union of $(n+\ell-3)$-dimensional orthants and so has dimension $n+\ell-3$ (for $n=4$, $\ell=1$: $2$, not $6$), while the proof of their Theorem 2.2 counts the distinct nontrivial splits of the cluster, which Grindstaff–Owen (proof of Proposition 3.8) restate as the number of vertices of the connection graph.
3. Every set of pairwise compatible splits in $G_{T_s,n,\ell}$ induces a clique and spans an orthant of $S_{T_s,n,\ell}$ of the same dimension.

## Expansion

1. Attaching the $j$th new leaf to a tree with $n+j-1$ leaves has $2(n+j-1)-3$ choices of edge, so the cluster size is the product $\prod_{j=1}^{\ell}(2(n+j)-5)$.
2. The vertex count is the number of distinct nontrivial splits of the trees in the cluster, counted in the proof of Theorem 2.2 of Ren et al. and restated as the vertex count of the connection graph in the proof of Proposition 3.8 of Grindstaff-Owen.

## Sources

- Yingying Ren, Sihan Zha, Jingwen Bi, José A. Sanchez, Cara Monical, Michelle Delcourt, Rosemary K. Guzman and Ruth Davidson, *A combinatorial method for connecting BHV spaces representing different numbers of taxa*, arXiv:1708.02626 (Theorems 2.1, 2.2 and 2.8; Corollary 2.4). <https://doi.org/10.48550/arXiv.1708.02626>
- Gillian Grindstaff and Megan Owen, *Geometric comparison of phylogenetic trees with different leaf sets* (published as *Representations of partial leaf sets in phylogenetic tree space*), arXiv:1807.04235 (proof of Proposition 3.8). <https://doi.org/10.48550/arXiv.1807.04235> Published version: SIAM Journal on Applied Algebra and Geometry 3 (2019) 691–720, <https://doi.org/10.1137/18M1235855>.
- L. J. Billera, S. P. Holmes, K. Vogtmann, Geometry of the space of phylogenetic trees, *Adv. Appl. Math.* 27 (2001), 733–767. <https://doi.org/10.1006/aama.2001.0759>
