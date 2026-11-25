# Spectral criterion's derivative in $\sigma_g^2$ at positive variances

Let $r$ be a finite index set, $d, w \in \mathbb{R}^r$ and $\theta = (\sigma_g^2, \sigma_e^2)$ a
parameter at which every [contrast variance](contrast-var.md)
$\lambda_i(\theta) = \sigma_g^2 d_i + \sigma_e^2$ is positive. Then $s \mapsto \ell(s, \sigma_e^2)$,
the [spectral REML criterion](spectral-log-lik.md) with $\sigma_e^2$ fixed, is differentiable at
$s = \sigma_g^2$, with derivative the [score](score-g.md)

$$\frac{\partial \ell}{\partial \sigma_g^2}(\theta) = \frac12 \sum_{i \in r}
\frac{d_i \, (w_i^2 - \lambda_i(\theta))}{\lambda_i(\theta)^2}.$$
