# Safety radius of the tropical projection onto M-ultrametrics

**Setting.** Let $M$ be a matroid on the ground set $[q]$. The **space of $M$-ultrametrics** $\mathcal U_M \subset \mathbb{R}^q/\mathbb{R}\mathbf 1$ is the set of $w$ such that, for every circuit $C$ of $M$, the maximum of $w_e$ over $e \in C$ is attained at least twice; it is the Bergman fan of $M$, and its vertices as a tropical polytope are indexed by the maximal proper flats of $M$. For the graphic matroid of the complete graph $K_p$ (so $q = \binom p2$), $\mathcal U_M$ is the space of ultrametrics on $p$ points, i.e. of equidistant trees with $p$ leaves. The tropical projective torus $\mathbb{R}^q/\mathbb{R}\mathbf 1$ carries the tropical metric

$$d_{\mathrm{tr}}(x, y) = \max_i (y_i - x_i) - \min_i (y_i - x_i),$$

and $\pi_M : \mathbb{R}^q/\mathbb{R}\mathbf 1 \to \mathcal U_M$ is the tropical projection onto the tropical polytope $\mathcal U_M$, which returns a $d_{\mathrm{tr}}$-nearest point and is non-expansive: $d_{\mathrm{tr}}(\pi_M x, \pi_M y) \le d_{\mathrm{tr}}(x, y)$. Give $\mathcal U_M$ the nested set fan structure; for $K_p$ its maximal cones are the binary tree topologies. For $w$ in a maximal cone set

$$w_{\min} = \min_C \Big(\max\nolimits^{1}_{e \in C} w_e - \max\nolimits^{2}_{e \in C} w_e\Big),$$

the smallest gap between the largest and second-largest coordinate over circuits (for $K_p$, the shortest internal edge length of the binary equidistant tree). The **safety radius** of $\pi_M$ is the largest $s \ge 0$ such that for every $w$ in the relative interior of a maximal cone $K$, $\pi_M(w + \epsilon)$ lies in the relative interior of $K$ for every $\epsilon \in (-s\,w_{\min}, s\,w_{\min})^q$.

**Statement.** For every matroid $M$, the safety radius of the tropical projection $\pi_M$ onto $\mathcal U_M$ is exactly $1/2$. In particular, projecting a dissimilarity vector whose entries are within $w_{\min}/2$ of those of an ultrametric of a binary equidistant tree recovers that tree's topology.

## Expansion

The tropical distance from $w$ in the relative interior of a maximal cone $K$ to the boundary of $K$ equals $w_{\min}$: one must close the gap between the top two coordinates on some circuit. A perturbation in the open cube of half-width $w_{\min}/2$ moves $w$ by tropical distance less than $w_{\min}$, and non-expansivity of $\pi_M$ (with $\pi_M w = w$) keeps $\pi_M(w + \epsilon)$ within that distance of $w$, hence inside $K$. A perturbation raising the second-largest and lowering the largest coordinate on the critical circuit by $w_{\min}/2$ each reaches the boundary, so $1/2$ cannot be improved.

## Sources

- S. Cox, J. Sabol, R. Talbut and R. Yoshida, "Tropical Fermat–Weber points over spaces of $M$-ultrametrics", *Vietnam Journal of Mathematics* (2026), Theorem 9, Definitions 2, 5 and 8, Lemmas 6 and 7, Proposition 4, Definition 1, <https://doi.org/10.1007/s10013-026-00799-6> (preprint arXiv:2505.09584).
