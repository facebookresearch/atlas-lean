# Responsibilities of the full-covariance Gaussian mixture

For valid parameters
$\theta = (\pi_j, \mu_j, \Sigma_j)_{j\lt K}$, a point $x \in \mathbb{R}^d$ and a component $k$, write
$p_k(x) = \pi_k \, \mathcal{N}(x \mid \mu_k, \Sigma_k)$, where $\mathcal{N}(\cdot \mid \mu, \Sigma)$
is the multivariate Gaussian density. The responsibility of $k$ for $x$ is the posterior
probability of component $k$ given $x$ (the E-step),

$$r_k(x) = \frac{p_k(x)}{\sum_j p_j(x)}.$$

For data $(x_n)_{n\lt N}$ one writes $r_{nk} = r_k(x_n)$.
