# BHV connection spaces linking tree spaces with different numbers of taxa

Let $\mathrm{BHV}_n$ be the Billera-Holmes-Vogtmann space of unrooted phylogenetic trees with $n$ labelled leaves and nonnegative internal edge weights: one nonnegative orthant of dimension $n-3$ per binary tree topology, glued along faces where edge weights vanish, with the induced intrinsic geodesic metric (a CAT(0) space).

Fix an unweighted binary *start tree* $T_s$ with $n$ leaves and a *connection step* $\ell\ge1$. The **BHV connection cluster** $C_{T_s,n,\ell}$ is the set of binary trees on $n+\ell$ leaves obtained from $T_s$ by attaching $\ell$ new labelled leaves to arbitrary edges (including leaf edges and edges created by earlier attachments). The **BHV connection space** $S_{T_s,n,\ell}\subseteq\mathrm{BHV}_{n+\ell}$ is the union of the $(n+\ell-3)$-dimensional orthants of the trees in $C_{T_s,n,\ell}$ together with their faces. Its **connection graph** $G_{T_s,n,\ell}$ has one vertex per split occurring in a tree of the cluster (one per one-dimensional orthant), with two vertices adjacent when the splits are compatible.

**Theorem.**

1. $|C_{T_s,n,\ell}| = \dfrac{(2(n+\ell)-5)!!}{(2n-5)!!}$.
2. $S_{T_s,n,\ell}$ has dimension $2^{\ell}(2n-2)-\ell-n-1$.
3. $S_{T_s,n,\ell}$ is convex in $\mathrm{BHV}_{n+\ell}$: the geodesic between any two trees of $S_{T_s,n,\ell}$ stays in $S_{T_s,n,\ell}$.
4. Every set of pairwise compatible splits in $G_{T_s,n,\ell}$ induces a clique and spans an orthant of $S_{T_s,n,\ell}$ of the same dimension.
5. For $\ell=1$, the largest independent set of $G_{T_s,n,1}$ has size $n$, and it is unique: the splits created by attaching the new leaf to the $n$ leaf edges. Moreover $G_{T_s,n,1}$ has exactly $\tfrac52(n-2)(n-3)$ edges.

Convexity means that geodesics, Fréchet means and consensus computations for trees on $n+\ell$ taxa that all refine a common $n$-taxon tree can be carried out inside the connection space, which is how trees on different taxon sets are compared.

## Expansion

1. Attaching the $j$th new leaf to a tree with $n+j-1$ leaves has $2(n+j-1)-3$ choices of edge, so the cluster size is the product $\prod_{j=1}^{\ell}(2(n+j)-5)$.
2. Convexity follows from the Owen-Provan description of BHV geodesics: a geodesic between two trees passes only through orthants whose splits are compatible with the common structure, and every tree whose restriction to the original leaves is $T_s$ lies in the connection space.
3. For $\ell=1$, splitting an internal edge of $T_s$ into subtrees $T_a,T_b$ with $a+b=n+2$ gives $|E(G_{T_s,n,1})|=|E(G_{T_a,a,1})|+|E(G_{T_b,b,1})|+5(a-2)(b-2)$; induction yields the closed form.

## Sources

- Y. Ren, S. Zha, J. Bi, J. A. Sanchez, *A combinatorial method for connecting BHV spaces representing different numbers of taxa*, arXiv:1708.02626 (Theorems 2.1, 2.2, 2.6, 2.7 and 2.8; Corollaries 2.4 and 2.9). <https://doi.org/10.48550/arXiv.1708.02626>
- L. J. Billera, S. P. Holmes, K. Vogtmann, Geometry of the space of phylogenetic trees, *Adv. Appl. Math.* 27 (2001), 733–767. <https://doi.org/10.1006/aama.2001.0759>
