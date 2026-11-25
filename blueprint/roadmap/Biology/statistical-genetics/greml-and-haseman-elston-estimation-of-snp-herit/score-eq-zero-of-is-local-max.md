# Spectral score equations at a local maximizer with positive variances

Let $r$ be a finite index set and $d, w \in \mathbb{R}^r$. If $\theta = (\sigma_g^2, \sigma_e^2)$
is a local maximizer in $\mathbb{R}^2$ of the [spectral REML criterion](spectral-log-lik.md) and
every [contrast variance](contrast-var.md) $\lambda_i(\theta) = \sigma_g^2 d_i + \sigma_e^2$ is
positive, then both [scores](score-g.md) vanish at $\theta$:

$$\sum_{i \in r} \frac{d_i \, (w_i^2 - \lambda_i(\theta))}{\lambda_i(\theta)^2} = 0
\qquad \text{and} \qquad \sum_{i \in r} \frac{w_i^2 - \lambda_i(\theta)}{\lambda_i(\theta)^2} = 0.$$
