# Doob's $L^2$ maximal inequality

Let $\mu$ be a probability measure and let $(f_k)_{k \in \mathbb{N}}$ be a real-valued martingale with respect to a filtration $(\mathcal{F}_k)$ and $\mu$ such that every $f_k$ is square-integrable. Then for every $n \in \mathbb{N}$, $\mathbb{E}\big[(\max_{k \le n} |f_k|)^2\big] \le 4\, \mathbb{E}[f_n^2]$.

## Idea

The running maximum of a martingale is controlled by its final value alone. Since $|f_k|$ is a submartingale, Doob's maximal inequality gives, with $M = \max_{k \le n} |f_k|$,
$\lambda\, P(M \ge \lambda) \le \mathbb{E}[|f_n| \mathbf{1}_{\{M \ge \lambda\}}]$ for every $\lambda > 0$. Integrating both sides against $2 \, d\lambda$ over $\lambda > 0$ gives $\mathbb{E}[M^2] \le 2\, \mathbb{E}[M |f_n|]$, and the Cauchy–Schwarz inequality turns this into $\|M\|_2 \le 2 \|f_n\|_2$, hence the constant $4$. In $L^p$, $1 < p < \infty$, the same argument gives the constant $(p/(p-1))^p$. The inequality turns convergence in $L^2$ into uniform control of whole paths; it is used for the convergence of square-integrable martingales and in the construction of stochastic integrals. The card also holds finite- and infinite-horizon forms bounded by the predictable quadratic variation, for martingales starting at $0$, and continuous-time versions.

## Statements

- [Doob's L² maximal inequality, finite horizon](doob-sq-maximal-ineq.md)
- [Doob's L² maximal inequality, infinite horizon](doob-sq-maximal-ineq-i-sup.md): infinite horizon, bounded by the predictable quadratic variation
- [Doob's L² maximal inequality in terms of the predictable quadratic variation, finite horizon](doob-sq-maximal-ineq-predictable-quadrat.md): form with the predictable quadratic variation
- [Predictable quadratic variation](predictable-quadratic-variation.md): definition used by the quadratic-variation form
- [Expectation of the predictable quadratic variation](integral-predictable-quadratic-variation.md): lemma used for the quadratic-variation form
- [Doob's $L^2$ maximal inequality in continuous time](lintegral-i-sup-sq-le-of-continuous.md): continuous-time form
- [Doob's $L^p$ maximal inequality in continuous time](lintegral-i-sup-rpow-le.md): continuous-time $L^p$ form for nonnegative submartingales (more general)

## Background

- [Convex functions of martingales](../convex-functions-of-martingales/README.md)
- [Doob's $L^p$ maximal inequality](../doob-s-lp-maximal-inequality/README.md): the $L^p$ inequality for submartingales, whose martingale case $p = 2$ is the main statement here
