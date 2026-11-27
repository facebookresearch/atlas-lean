# Distribution function of a weighted sum of a flat Dirichlet vector

Let $n \ge 1$, let $\theta = (\theta_0, \dots, \theta_n) \sim \operatorname{Dir}(1, \dots, 1)$ be a
flat [Dirichlet](../dirichlet-law/dirichlet-measure.md) random vector in $\mathbb{R}^{n+1}$, and let
$w_0, \dots, w_n$ be pairwise distinct real weights. Then for every real $x$,

$$P\Bigl(\sum_{j=0}^n w_j \theta_j \le x\Bigr) = (-1)^n \sum_{j=0}^n \frac{\max(x - w_j, 0)^n}{\prod_{m \ne j} (w_j - w_m)} .$$

The weights may have any signs and need not be sorted; the sum runs over all $n + 1$ nodes.
