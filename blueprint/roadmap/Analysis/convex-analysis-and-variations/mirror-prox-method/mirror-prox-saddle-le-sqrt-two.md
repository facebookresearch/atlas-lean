# The $O(1/N)$ saddle-point accuracy of mirror-prox with the step $\alpha / (\sqrt{2} L)$

In the setting of the [saddle-point bound](mirror-prox-saddle-le.md) with $L > 0$, the step $\gamma = \alpha / (\sqrt{2}L)$ and $V_{z_0} \le \Theta$ on $X \times Y$,

$$
f(\bar x_N, y) - f(x, \bar y_N) \le \frac{\sqrt{2}\,\Theta L}{\alpha N} \qquad \text{for all } x \in X,\ y \in Y .
$$

Taking the supremum over $y$ and the infimum over $x$, the gap $\sup_{y \in Y} f(\bar x_N, y) - \inf_{x \in X} f(x, \bar y_N)$ is at most $\sqrt{2}\Theta L/(\alpha N)$. The source's accuracy $\epsilon_f(\bar z_N)$, the sum of $\max_y f(\bar x_N, y) - \min_x \max_y f$ and $\max_y \min_x f - \min_x f(x, \bar y_N)$, is at most this gap, with equality when $\min_x \max_y f = \max_y \min_x f$, as for convex compact $X$ and $Y$. For a matrix game, the bilinear $x^T A y$ on $\Delta_p \times \Delta_q$ with the entropy-type setups of the source on both simplices, this gives $\epsilon_f(\bar z_N) \le O(1) \max_{i,j}|A_{ij}| \sqrt{\ln(p+1)\ln(q+1)}/N$ at the cost of four matrix-vector products per step.

## Sources

- A. Nemirovski, *Prox-method with rate of convergence O(1/t) for variational inequalities with Lipschitz continuous monotone operators and smooth convex-concave saddle point problems*, SIAM J. Optim. 15(1) (2004), 229–251; author PDF at <https://www2.isye.gatech.edu/~nemirovs/SIOPT_042562-1.pdf>, Section 3, Theorem 3.2, efficiency estimate (3.10), with the step (3.2); matrix games are Example 1 of Section 5, efficiency estimate (5.14).
