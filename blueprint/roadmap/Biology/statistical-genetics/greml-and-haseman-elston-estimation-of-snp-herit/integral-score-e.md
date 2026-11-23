# The REML score for $\sigma_e^2$ has mean zero at the true parameter

Let $m$, $k$ and $r$ be finite index sets, $X$ a real $m \times k$ matrix, $K$ a real $m \times m$
matrix, $B$ a real $r \times m$ matrix and $d \in \mathbb{R}^r$ with $BX = 0$, $BB^\top = I$,
$|r| + |k| = |m|$ and $BKB^\top = \operatorname{diag}(d)$
([diagonalizing orthonormal error contrast](is-spectral-contrast.md)). Let
$\theta_0 = (\sigma_{g,0}^2, \sigma_{e,0}^2)$ be such that
$V(\theta_0) = \sigma_{g,0}^2 K + \sigma_{e,0}^2 I$ is positive semidefinite and every
[contrast variance](contrast-var.md) $\lambda_i(\theta_0) = \sigma_{g,0}^2 d_i + \sigma_{e,0}^2$
is positive, let $\beta \in \mathbb{R}^k$, and let $y$ be a random vector in $\mathbb{R}^m$ on a
probability space $(\Omega, \mu)$ with law $N(X\beta, V(\theta_0))$. Then the
[REML score](score-e.md) for $\sigma_e^2$ at $\theta_0$ of the rotated contrasts $w = By$,

$$U_e(\theta_0) = \frac12 \sum_{i \in r}
\frac{w_i^2 - \lambda_i(\theta_0)}{\lambda_i(\theta_0)^2},$$

is integrable, since each $w_i^2$ is ([second moments](integral-sq-contrast.md)), and has mean
zero: $\mathbb{E}[U_e(\theta_0)] = 0$.
