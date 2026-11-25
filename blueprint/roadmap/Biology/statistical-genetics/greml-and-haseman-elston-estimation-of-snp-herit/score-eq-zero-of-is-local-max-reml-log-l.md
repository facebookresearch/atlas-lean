# REML score equations at a local maximizer with positive variances

Let $m$ and $r$ be finite index sets, $K$ a real $m \times m$ matrix, $B$ a real $r \times m$
matrix with $BB^\top = I$ and $BKB^\top = \operatorname{diag}(d)$, and $y \in \mathbb{R}^m$. For
$\varphi = (\varphi_1, \varphi_2) \in \mathbb{R}^2$ let $\ell_B(\varphi)$ be the restricted
log-likelihood of $y$ for $B$ at the [GREML covariance](greml-cov.md)
$V(\varphi) = \varphi_1 K + \varphi_2 I$: the logarithm of the density of the Gaussian law
$N(0, B V(\varphi) B^\top)$ at $By$. If $\theta = (\sigma_g^2, \sigma_e^2)$ is a local maximizer
of $\ell_B$ in $\mathbb{R}^2$ at which every [contrast variance](contrast-var.md)
$\lambda_i(\theta) = \sigma_g^2 d_i + \sigma_e^2$ is positive (an interior REML estimate), then
both REML [scores](score-g.md) of the rotated contrasts $w = By$ vanish at $\theta$:

$$\sum_{i \in r} \frac{d_i \, (w_i^2 - \lambda_i(\theta))}{\lambda_i(\theta)^2} = 0
\qquad \text{and} \qquad \sum_{i \in r} \frac{w_i^2 - \lambda_i(\theta)}{\lambda_i(\theta)^2} = 0.$$
