# $f_2$ distances to a two-way mixture on a scaffold tree

**Setting.** Let $\mathcal T$ be a tree of unadmixed populations carrying a drift model: allele frequencies are the root frequency plus orthogonal, mean-zero drift increments on the edges, with second moment $\ell_e$ on edge $e$. Then $f_2(P, Q) = d_{\mathcal T}(P, Q)$, the sum of edge lengths on the path between $P$ and $Q$, and the same holds for points in the interior of edges after subdividing them.

A population $M$ is formed by a single admixture event: a lineage splits from the point $A'$ on edge $e_1$ and drifts by $x$, a lineage splits from the point $B'$ on edge $e_2$ and drifts by $y$, the two mix in proportions $\alpha$ and $1 - \alpha$, and the mixture then drifts by $z$, with all these increments orthogonal to each other and to the tree increments:

$$p_M = \alpha\,(p_{A'} + \delta_x) + (1 - \alpha)\,(p_{B'} + \delta_y) + \delta_z .$$

**Proposition.** For every population $P$ of the scaffold tree,

$$f_2(M, P) = \alpha\, d_{\mathcal T}(A', P) + (1 - \alpha)\, d_{\mathcal T}(B', P) - \alpha(1 - \alpha)\, d_{\mathcal T}(A', B') + D,$$

$$D = \alpha^2 x + (1 - \alpha)^2 y + z .$$

If $A'$ lies at distance $a$ from the upper end of $e_1$ and $B'$ at distance $b$ from the upper end of $e_2$, each $d_{\mathcal T}$ term is affine in $(a, b)$. Hence, for fixed $\alpha$, the system of equations $f_2(M, P) = \hat f_2(M, P)$ over all scaffold populations $P$ is **linear** in the three unknowns $(a, b, D)$, and only the combination $D$ ("mixed drift") of the three post-split drift lengths is identifiable from these equations.

**Fitting.** With $n \ge 4$ scaffold populations one obtains $n$ equations in the four unknowns $(\alpha, a, b, D)$. For each candidate pair of edges $(e_1, e_2)$, minimize the residual sum of squares by constrained linear least squares in $(a, b, D)$ (with $0 \le a \le \ell_{e_1}$, $0 \le b \le \ell_{e_2}$, $D \ge 0$) inside a one-dimensional search over $\alpha \in [0, 1]$, and report the edge pair with the smallest residual. The equations give four independent constraints exactly when the scaffold contains two populations that branch from different points along the lineage joining the two split points (necessary and sufficient according to the source).

## Depends on

- [f2 statistic](../../patterson-s-f-statistics/f2.md)
- [Admixture-graph drift model](../../patterson-s-f-statistics/drift-model.md)

## Expansion

Write $u = p_{A'} - p_P$ and $w = p_{B'} - p_P$. Orthogonality of $\delta_x, \delta_y, \delta_z$ to everything else gives

$$f_2(M, P) = \mathbb E\bigl[(\alpha u + (1 - \alpha) w)^2\bigr] + \alpha^2 x + (1 - \alpha)^2 y + z .$$

The identity $(\alpha u + (1 - \alpha) w)^2 = \alpha u^2 + (1 - \alpha) w^2 - \alpha(1 - \alpha)(u - w)^2$, with $\mathbb E u^2 = d(A', P)$, $\mathbb E w^2 = d(B', P)$ and $\mathbb E(u - w)^2 = d(A', B')$, gives the formula. Moving $A'$ a distance $\varepsilon$ along $e_1$ changes $d(A', P)$ by $\pm\varepsilon$ (the sign depends on whether $P$ lies below $e_1$) and changes $d(A', B')$ by $\pm\varepsilon$ when $e_1 \ne e_2$, so all terms are affine in $(a, b)$; $\alpha$ enters nonlinearly only through the coefficients. In practice the equations are slightly inconsistent because of sampling noise and departures from the point-admixture model, so least squares is used, and bootstrap resampling over genome blocks and individuals gives confidence intervals.

## Sources

- M. Lipson, P.-R. Loh, A. Levin, D. Reich, N. Patterson, B. Berger, *Efficient moment-based inference of admixture parameters and sources of gene flow*, Molecular Biology and Evolution 30 (2013), <https://doi.org/10.1093/molbev/mst099>, PMCID PMC3708505. Materials and Methods, "Model Assumptions and f-Statistics", "Two-Way Admixture Fitting" (four unknowns, $n$ equations, linearity for fixed $\alpha$, constrained least squares inside a search over $\alpha$) and Figure 2 (Branch1Loc, Branch2Loc, $\alpha$, MixedDrift), including the identifiability condition; supplementary text S1. The closed form of $f_2(M,P)$ is derived here from the drift model.
