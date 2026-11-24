# Contrast variances $\sigma_g^2 d_i + \sigma_e^2$

For a real vector $d = (d_i)_{i \in r}$ indexed by a finite set $r$, a parameter
$\theta = (\sigma_g^2, \sigma_e^2) \in \mathbb{R}^2$ and an index $i$,

$$\lambda_i(\theta) = \sigma_g^2 d_i + \sigma_e^2,$$

for all real values, negative ones included. When $B$ is an orthonormal error contrast with
$BKB^\top = \operatorname{diag}(d)$ ([diagonalizing contrast](is-spectral-contrast.md)) and
$y \sim N(X\beta, \sigma_g^2 K + \sigma_e^2 I)$ with a positive semidefinite covariance,
$\lambda_i(\theta)$ is the variance of the rotated contrast $w_i = (By)_i$, which has mean $0$ and
second moment $\lambda_i(\theta)$ ([second moments](integral-sq-contrast.md)).
