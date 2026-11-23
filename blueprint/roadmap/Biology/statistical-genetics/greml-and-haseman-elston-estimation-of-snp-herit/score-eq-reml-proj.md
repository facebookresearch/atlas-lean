# REML scores in GCTA's matrix form at positive contrast variances

Let $m$ and $r$ be finite index sets, $K$ a real $m \times m$ matrix, $B$ a real $r \times m$
matrix with $BB^\top = I$ and $BKB^\top = \operatorname{diag}(d)$, and
$\theta = (\sigma_g^2, \sigma_e^2)$ a parameter at which every
[contrast variance](contrast-var.md) $\lambda_i(\theta) = \sigma_g^2 d_i + \sigma_e^2$ is
positive. Let $P = B^\top (B V(\theta) B^\top)^{-1} B$ be the [REML projection](reml-proj.md) at
the [GREML covariance](greml-cov.md) $V(\theta) = \sigma_g^2 K + \sigma_e^2 I$; here
$B V(\theta) B^\top = \operatorname{diag}(\lambda_i(\theta))_i$ is invertible. Then for every
$y \in \mathbb{R}^m$ the [scores](score-g.md) of the rotated contrasts $w = By$ are

$$\frac12 \sum_{i \in r} \frac{d_i \, (w_i^2 - \lambda_i(\theta))}{\lambda_i(\theta)^2}
= \frac{y^\top P K P y - \operatorname{tr}(P K)}{2}, \qquad
\frac12 \sum_{i \in r} \frac{w_i^2 - \lambda_i(\theta)}{\lambda_i(\theta)^2}
= \frac{y^\top P P y - \operatorname{tr} P}{2}.$$
