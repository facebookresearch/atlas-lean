# Closest-point projection onto tree-space lines and existence of principal lines

**Setting.** Let $\mathcal T_O$ be the Billera–Holmes–Vogtmann (BHV) space of unrooted metric phylogenetic trees on a fixed taxon set $O$: each fully resolved topology $t$ contributes a nonnegative orthant $Q_t$ whose coordinates are the internal branch lengths, orthants are glued along faces where branch lengths vanish, pendant branch lengths contribute a common Euclidean factor, and $d$ is the induced geodesic (path-length) metric. $\mathcal T_O$ is a complete CAT(0) space, so any two trees are joined by a unique geodesic, and locally geodesic paths are globally geodesic.

A path $\Gamma \subset \mathcal T_O$ is a *$\mathcal T_O$-line* if every sub-path of $\Gamma$ is the geodesic between its endpoints and $\Gamma$ extends to infinity in both directions. Every geodesic segment extends (not necessarily uniquely) to a $\mathcal T_O$-line.

**Proposition 2.1 (projection).** For every $\mathcal T_O$-line $L$ and every tree $x \in \mathcal T_O$ there is a unique point $y \in L$ minimizing $d(x, y)$ over $L$. Moreover, if $x_0 \in L$ and $L(t)$ is the arc-length parametrization with $L(0) = x_0$, then $y = L(t^*)$ for some $|t^*| \le d(x_0, x)$.

**Proposition 2.2 (principal lines exist).** Let $x_0, x_1, \dots, x_n \in \mathcal T_O$, and for a line $L$ through $x_0$ let $y_i$ be the projection of $x_i$ onto $L$. Define

$$ f_\parallel(L) = \sum_{i=1}^n d(x_0, y_i)^2, \qquad f_\perp(L) = \sum_{i=1}^n d(x_i, y_i)^2 . $$

Then some $\mathcal T_O$-line through $x_0$ maximizes $f_\parallel$, and some $\mathcal T_O$-line through $x_0$ minimizes $f_\perp$. The optimizer need not be unique: a geodesic can admit several extensions to a line, and isotropic data have many optimal directions, as in Euclidean PCA.

## Depends on

- [The space of phylogenetic trees is CAT(0)](../../../not-yet-classified/phylogenetic-tree-space/tree-space-is-cat0.md)
- [Geodesics in tree space are unique](../../../not-yet-classified/phylogenetic-tree-space/tree-space-geodesic-unique.md)

## Expansion

For Proposition 2.1, put $r = d(x_0, x)$. The CAT(0) comparison ("skinny triangle") property applied to the triangle $x_0, x, L(t)$ with $t > r$ gives $d(x, L(r)) < d(x, L(t))$, and likewise for $L(-t)$, so a minimizer lies in the compact arc $L([-r, r])$, where the continuous function $t \mapsto d(x, L(t))$ attains its minimum. If two distinct points $y, y'$ of $L$ were both at the minimal distance $\rho$, the comparison property for the triangle $y, x, y'$ would put points of $L$ strictly between them at distance less than $\rho$, a contradiction. For Proposition 2.2, set $R = \max_i d(x_0, x_i)$; all projections lie within distance $R$ of $x_0$, so both objectives depend on a line only through its pair of points $(z, z')$ at distance $R$ from $x_0$, which are *antipodal* ($d(z, z') = 2R$). Antipodal pairs form a closed, hence compact, subset of $S_R \times S_R$ for the sphere $S_R$ of radius $R$ about $x_0$, so continuous objectives attain their optima there, and the optimal geodesic extends to a line. In practice $x_0$ is a Fréchet mean (centroid) of the sample, geodesic distances are computed with the polynomial-time Owen–Provan algorithm, and the optimal line is searched for by greedy or Monte Carlo moves through the orthant structure; maximizing $f_\parallel$ was found to recover principal directions more reliably than minimizing $f_\perp$, which unlike the Euclidean case are not equivalent objectives.

## Sources

- Tom M. W. Nye, "Principal components analysis in the space of phylogenetic trees", Annals of Statistics 39(5) (2011); arXiv:1202.5132, Section 1 (geometry of tree space), Section 2.1 (Definition 1, Propositions 2.1 and 2.2), Sections 2.2–2.6 (centroids, projection, optimization). <https://doi.org/10.48550/arXiv.1202.5132>. Published version: The Annals of Statistics 39(5) (2011), 2716–2739, <https://doi.org/10.1214/11-aos915>; locators above refer to the arXiv version.
