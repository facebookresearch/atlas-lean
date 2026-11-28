# BHV connection spaces linking tree spaces with different numbers of taxa

Let $\mathrm{BHV}_n$ be the Billera-Holmes-Vogtmann space of unrooted phylogenetic trees with $n$ labelled leaves and nonnegative internal edge weights: one nonnegative orthant of dimension $n-3$ per binary tree topology, glued along faces where edge weights vanish, with the induced intrinsic geodesic metric (a CAT(0) space).

Fix an unweighted binary *start tree* $T_s$ with $n$ leaves and a *connection step* $\ell\ge1$. The **BHV connection cluster** $C_{T_s,n,\ell}$ is the set of binary trees on $n+\ell$ leaves obtained from $T_s$ by attaching $\ell$ new labelled leaves to arbitrary edges (including leaf edges and edges created by earlier attachments). The **BHV connection space** $S_{T_s,n,\ell}\subseteq\mathrm{BHV}_{n+\ell}$ is the union of the $(n+\ell-3)$-dimensional orthants of the trees in $C_{T_s,n,\ell}$ together with their faces. Its **connection graph** $G_{T_s,n,\ell}$ has one vertex per split occurring in a tree of the cluster (one per one-dimensional orthant), with two vertices adjacent when the splits are compatible.

**Theorem.**

1. $|C_{T_s,n,\ell}| = \dfrac{(2(n+\ell)-5)!!}{(2n-5)!!}$.
2. Every set of pairwise compatible splits in $G_{T_s,n,\ell}$ induces a clique and spans an orthant of $S_{T_s,n,\ell}$ of the same dimension.

## Expansion

1. Attaching the $j$th new leaf to a tree with $n+j-1$ leaves has $2(n+j-1)-3$ choices of edge, so the cluster size is the product $\prod_{j=1}^{\ell}(2(n+j)-5)$.

## Sources

- Yingying Ren, Sihan Zha, Jingwen Bi, José A. Sanchez, Cara Monical, Michelle Delcourt, Rosemary K. Guzman and Ruth Davidson, *A combinatorial method for connecting BHV spaces representing different numbers of taxa*, arXiv:1708.02626 (Theorems 2.1 and 2.8; Corollary 2.4). <https://doi.org/10.48550/arXiv.1708.02626>
- Gillian Grindstaff and Megan Owen, *Geometric comparison of phylogenetic trees with different leaf sets* (published as *Representations of partial leaf sets in phylogenetic tree space*), arXiv:1807.04235 (Lemma 3.7 and the proof of Proposition 3.6). <https://doi.org/10.48550/arXiv.1807.04235> Published version: SIAM Journal on Applied Algebra and Geometry 3 (2019) 691–720, <https://doi.org/10.1137/18M1235855>.
- L. J. Billera, S. P. Holmes, K. Vogtmann, Geometry of the space of phylogenetic trees, *Adv. Appl. Math.* 27 (2001), 733–767. <https://doi.org/10.1006/aama.2001.0759>
