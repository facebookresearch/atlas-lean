# Locus of the weighted Fréchet mean in BHV tree space

**Setting.** Let $\mathcal T$ be the BHV space of rooted phylogenetic trees with edge lengths on a fixed leaf set (pendant edges dropped), a union of nonnegative orthants $\mathbb{R}_{\ge0}^{m}$, one per fully resolved topology, glued along faces; with the induced geodesic metric $d$ it is CAT(0), so geodesics are unique and squared distance is strictly convex along geodesics. For vertex trees $T_0,\dots,T_k \in \mathcal T$ and weights $w$ in the simplex $\Delta_k = \{w \in \mathbb{R}_{\ge0}^{k+1} : \sum_i w_i = 1\}$, the weighted Fréchet mean

$$\mu(w) = \arg\min_{T\in\mathcal T}\ \sum_{i=0}^k w_i\, d(T, T_i)^2$$

exists and is unique. The *locus of the weighted Fréchet mean* is $\mathcal L(T_0,\dots,T_k) = \{\mu(w) : w \in \Delta_k\}$, the tree-space analogue of the affine span of $k+1$ points, used as a $k$-th order principal locus.

A geodesic between fully resolved trees is *simple* if at most one edge length contracts to zero at a time as it is traversed. Fixing a fully resolved orthant $\mathcal O$, a *support region* is a set of $T \in \mathcal O$ on which the combinatorial support of the geodesic from $T$ to a given vertex tree is constant; a *mutual support region* is an intersection of support regions, one for each vertex tree.

**Theorem.**
1. If, on a mutual support region, all geodesics from $T$ to the vertex trees are simple, then $\mathcal L$ restricted to that region is contained in an affine subspace of dimension at most $k$.
2. Within any mutual support region in a fully resolved orthant, the matrix of second derivatives of $T \mapsto \sum_i w_i d(T,T_i)^2$ with respect to the internal edge lengths is positive definite, and $\mathcal L$ is a submanifold of dimension at most $k$; for generic vertex trees its dimension is exactly $k$.

## Depends on

- [BHV tree space is CAT(0)](../../../not-yet-classified/phylogenetic-tree-space/tree-space-is-cat0.md)

## Expansion

Within a support region the squared distance from $T$ to $T_i$ is a fixed smooth function of the edge lengths of $T$ (sums of squared Euclidean norms of blocks of edge lengths, with constants determined by $T_i$), and it is continuously differentiable across the whole orthant. The Fréchet mean is characterized by the stationarity equation $\sum_i w_i\nabla_T d(T,T_i)^2 = 0$. For simple geodesics each block contains a single split, so the gradient is affine in $T$, and solving the stationarity equation writes each edge length as a linear combination of $w_0,\dots,w_k$: an affine image of the simplex. In general, positive definiteness of this second-derivative matrix lets the implicit function theorem solve the stationarity equation locally as a smooth function $T = \mu(w)$, whose image has dimension $k$ when its derivative has full rank $k$, which holds for generic vertex trees. Weighted Fréchet means are computed with Sturm's stochastic algorithm, and projection onto $\mathcal L$ by a geometric descent over the simplex.

## Sources

- T. M. W. Nye, X. Tang, G. Weyenberg, R. Yoshida, "Principal component analysis and the locus of the Fréchet mean in the space of phylogenetic trees", Biometrika (2017), Definitions 1–2, Lemmas 1–2, Theorem 1 and Algorithms 1–3, <https://doi.org/10.1093/biomet/asx047>, PMCID PMC5793493.
