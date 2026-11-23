# Pseudoreplication understates the variance at positive donor variance

Let $\sigma_b^2 > 0$, let $\sigma_e^2$ be any real number, and let $D \ge 1$ and $m \ge 2$. Then the
[naive variance](naive-var.md) $V_{\mathrm{naive}}(D, m) = (\sigma_b^2 + \sigma_e^2) / (D m)$ is
strictly smaller than the [true variance](true-var.md)
$V_{\mathrm{true}}(D, m) = \sigma_b^2 / D + \sigma_e^2 / (D m)$. With at least two cells per donor,
treating the cells of a [random-intercept model](is-random-intercept.md) with positive donor
variance as independent replicates understates the variance of the cell-level mean.
