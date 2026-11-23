# REML log-likelihood in spectral form at positive contrast variances

Let $m$ and $r$ be finite index sets, $K$ a real $m \times m$ matrix and $B$ a real $r \times m$
matrix with orthonormal rows, $BB^\top = I$, such that $BKB^\top = \operatorname{diag}(d)$. Let
$\theta = (\sigma_g^2, \sigma_e^2)$ be a parameter at which every
[contrast variance](contrast-var.md) $\lambda_i(\theta) = \sigma_g^2 d_i + \sigma_e^2$ is
positive. Then for every $y \in \mathbb{R}^m$, the restricted log-likelihood $\ell_B(\theta)$ of
$y$ for $B$ at the [GREML covariance](greml-cov.md) $V(\theta) = \sigma_g^2 K + \sigma_e^2 I$, the
logarithm of the density of the Gaussian law $N(0, B V(\theta) B^\top)$ at $By$, is the
[spectral criterion](spectral-log-lik.md) at the rotated contrasts $w = By$:

$$\ell_B(\theta) = -\frac{|r|}{2} \log(2\pi) - \frac12 \sum_{i \in r} \log \lambda_i(\theta) -
\frac12 \sum_{i \in r} \frac{w_i^2}{\lambda_i(\theta)}.$$

This is the case $Q = I$ of the [rotated form](reml-log-lik-eq-spectral-log-lik-of-orth.md).
