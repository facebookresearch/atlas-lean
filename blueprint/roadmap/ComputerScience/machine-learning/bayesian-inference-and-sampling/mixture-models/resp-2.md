# Responsibilities in an isotropic Gaussian mixture

For valid parameters $\theta$ with mixing
weights $\pi_k$, means $\mu_k$ and variances $\sigma_k^2$, a point $x \in \mathbb{R}^d$ and a
component $k$, the responsibility of $k$ for $x$ is the posterior
$p_\theta(k \mid x) = \pi_k \mathcal{N}(x \mid \mu_k, \sigma_k^2 I) /
\sum_j \pi_j \mathcal{N}(x \mid \mu_j, \sigma_j^2 I)$, where $\mathcal{N}(x \mid \mu, v I)$ is the
isotropic Gaussian density. Computing it at each data point is the E-step.
