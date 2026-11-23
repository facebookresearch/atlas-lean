# Neighbor joining averages up to row shifts

Let $d$ be a symmetric dissimilarity on a finite set $X$ with $d(x, x) = 0$, and let a [run of neighbor joining](../neighbor-joining/njrun.md) on $d$ reach the cluster set $S$ with cluster dissimilarity $D$. Then there are weights $\alpha_s : X \to \mathbb{R}$ and reals $\kappa_s$ such that for all $s, t \in S$:

- $\alpha_s(x) \ge 0$ for every $x$, $\alpha_s(x) = 0$ for $x \notin s$, and $\sum_x \alpha_s(x) = 1$;
- $D(s, s) = 0$;
- if $s \ne t$, then $D(s, t) = \sum_x \sum_y \alpha_s(x) \alpha_t(y) d(x, y) - \kappa_s - \kappa_t$.
