# Mixture density of an isotropic Gaussian mixture

For valid parameters $\theta$ with
mixing weights $\pi_k$, means $\mu_k$ and variances $\sigma_k^2$, and every $x \in \mathbb{R}^d$,
the marginal $p_\theta(x) = \sum_k p_\theta(x, k)$ of the joint density equals
$\sum_k \pi_k \, \mathcal{N}(x \mid \mu_k, \sigma_k^2 I)$, where $\mathcal{N}(x \mid \mu, v I)$
is the isotropic Gaussian density.
