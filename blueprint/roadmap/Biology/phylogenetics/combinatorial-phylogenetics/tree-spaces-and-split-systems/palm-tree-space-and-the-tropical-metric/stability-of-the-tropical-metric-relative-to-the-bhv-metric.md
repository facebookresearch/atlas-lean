# Stability of the tropical metric relative to the BHV metric

Fix $N \ge 4$ leaves and let $n = \binom{N}{2}$. Represent a phylogenetic tree $u$ on leaf set $[N]$, with nonnegative internal and external edge lengths, by its tree metric $w^u = (w^u_{ij})_{1 \le i < j \le N}$, where $w^u_{ij}$ is the sum of edge lengths on the path between leaves $i$ and $j$, viewed as a point of the tropical projective torus $\mathbb{R}^n/\mathbb{R}\mathbf{1}$. The tropical metric on $\mathbb{R}^n/\mathbb{R}\mathbf{1}$ is

$$ d_{\mathrm{tr}}([x],[y]) = \max_{1 \le i \le n}(x_i - y_i) - \min_{1 \le i \le n}(x_i - y_i), $$

and the palm tree space $\mathcal{P}_N$ is the space of trees with $N$ leaves equipped with $d_{\mathrm{tr}}$. Let $d_{\mathrm{BHV}}$ be the Billera–Holmes–Vogtmann geodesic metric on the same trees, extended to include external edge lengths (Euclidean within each orthant, with the external lengths forming an extra Euclidean factor).

**Theorem (stability).** For any two trees $u, u'$ with $N$ leaves,

$$ d_{\mathrm{tr}}(u, u') \le \sqrt{N+1}\, d_{\mathrm{BHV}}(u, u'), $$

and $\sqrt{N+1}$ is the smallest constant for which this holds for all pairs. No reverse inequality holds: there are distinct trees at tropical distance $0$ but positive BHV distance (the two spaces are not isometric).

## Expansion

Within one orthant, let $d_k$ be the differences of the internal edge lengths and $p_1,\dots,p_N$ those of the external edge lengths, so $d_{\mathrm{BHV}}(u,u')^2 = \sum_k d_k^2 + \sum_i p_i^2$. Each difference $w^u_{ij} - w^{u'}_{ij}$ is a sum of some $d_k$ plus $p_i + p_j$, so the largest minus the smallest such difference is at most $\sum_k |d_k|$ plus four of the $|p_i|$. Cauchy–Schwarz then bounds this sum by $\sqrt{N+1}$ times the Euclidean norm of the length differences. For trees in different orthants, cut the unique BHV geodesic into pieces lying in single orthants, apply the bound to each piece, and add them up using the triangle inequality for $d_{\mathrm{tr}}$. An explicit pair of caterpillar-type trees attains $d_{\mathrm{tr}} = N+1$ and $d_{\mathrm{BHV}} = \sqrt{N+1}$, so the constant is sharp.

The theorem means that a perturbation of a tree that is small in BHV distance stays small in palm tree space. Distance-threshold procedures such as single-linkage clustering therefore carry over from BHV space to the tropical setting. The same source shows that open tropical balls are open polytopes generating the Euclidean topology on $\mathbb{R}^{n-1}$ (Theorem 19), and that $\mathcal{P}_N$ is complete and separable (Propositions 21 and 22), so it supports Fréchet-type statistics.

## Sources

- A. Monod, B. Lin, R. Yoshida and Q. Kang, "Tropical Geometry of Phylogenetic Tree Space: A Statistical Perspective", arXiv:1805.12400 (2018), <https://doi.org/10.48550/arXiv.1805.12400>. Theorem 11 (stability), Definition 7 (tropical metric), Definition 9 (palm tree space), Theorem 19, Propositions 21–22. Published version: Vietnam Journal of Mathematics (2026), <https://doi.org/10.1007/s10013-026-00795-w>.
