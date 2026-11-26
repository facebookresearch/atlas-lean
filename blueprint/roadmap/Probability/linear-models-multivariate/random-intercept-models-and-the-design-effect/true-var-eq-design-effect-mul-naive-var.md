# Design effect relates the true and naive variances

For real $\sigma_b^2$ and $\sigma_e^2$ with $\sigma_b^2 + \sigma_e^2 \ne 0$ and natural numbers
$D \ne 0$ and $m \ne 0$,

$$V_{\mathrm{true}}(D, m) = \bigl(1 + (m - 1) \rho\bigr)\, V_{\mathrm{naive}}(D, m),$$

where $\rho = \sigma_b^2 / (\sigma_b^2 + \sigma_e^2)$ is the [intraclass correlation](icc.md),
$V_{\mathrm{true}}$ the [true variance](true-var.md) and $V_{\mathrm{naive}}$ the
[naive variance](naive-var.md). The factor $1 + (m - 1)\rho$ is the design effect of a cluster
sample (Kish 1965).
