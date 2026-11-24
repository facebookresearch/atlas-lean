# The closed-form REML estimator is unbiased when both eigenvalues occur

Let $m$, $k$ and $r$ be finite index sets, $X$ a real $m \times k$ matrix, $K$ a real $m \times m$
matrix, $B$ a real $r \times m$ matrix and $d \in \mathbb{R}^r$ with $BX = 0$, $BB^\top = I$,
$|r| + |k| = |m|$ and $BKB^\top = \operatorname{diag}(d)$
([diagonalizing orthonormal error contrast](is-spectral-contrast.md)). Let
$\theta_0 = (\sigma_{g,0}^2, \sigma_{e,0}^2)$ be such that
$V(\theta_0) = \sigma_{g,0}^2 K + \sigma_{e,0}^2 I$ is positive semidefinite, let
$\beta \in \mathbb{R}^k$, and let $y$ be a random vector in $\mathbb{R}^m$ on a probability space
$(\Omega, \mu)$ with law $N(X\beta, V(\theta_0))$. Let $a \ne b$ be reals each equal to $d_i$ for
at least one $i$; other eigenvalues may occur too. Then the
[closed-form estimate](two-level-reml.md) $(\hat\sigma_g^2, \hat\sigma_e^2)$ computed from
$w = By$ is integrable, its components being linear combinations of the integrable $w_i^2$, and

$$\mathbb{E}[\hat\sigma_g^2] = \sigma_{g,0}^2, \qquad \mathbb{E}[\hat\sigma_e^2] = \sigma_{e,0}^2.$$
