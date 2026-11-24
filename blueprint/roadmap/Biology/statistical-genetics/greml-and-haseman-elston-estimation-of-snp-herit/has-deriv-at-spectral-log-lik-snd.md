# Spectral criterion's derivative in $\sigma_e^2$ at positive variances

Let $r$ be a finite index set, $d, w \in \mathbb{R}^r$ and $\theta = (\sigma_g^2, \sigma_e^2)$ a
parameter at which every [contrast variance](contrast-var.md)
$\lambda_i(\theta) = \sigma_g^2 d_i + \sigma_e^2$ is positive. Then $s \mapsto \ell(\sigma_g^2, s)$,
the [spectral REML criterion](spectral-log-lik.md) with $\sigma_g^2$ fixed, is differentiable at
$s = \sigma_e^2$, with derivative the [score](score-e.md)

$$\frac{\partial \ell}{\partial \sigma_e^2}(\theta) = \frac12 \sum_{i \in r}
\frac{w_i^2 - \lambda_i(\theta)}{\lambda_i(\theta)^2}.$$
