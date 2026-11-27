# Frequency density averaged over a distribution of fitness effects

For a measure $\mu$ on $\mathbb{R}$ and real $\theta, x$, the averaged frequency density is

$$\varphi^\mu_\theta(x) = \int \varphi_{\theta,\sigma}(x) \, d\mu(\sigma),$$

where $\varphi_{\theta,\sigma}$ is the Poisson-random-field density with scaled selection coefficient $\sigma$ (see the [uniform bound](abs-expected-sfs-le.md)), with the convention that the integral of a non-integrable function is $0$. When $\mu$ is a probability measure, $\theta \ge 0$ and $0 < x < 1$, it is the expected density of sites at derived-allele frequency $x$ when each new mutation draws its own $\sigma$ from $\mu$.
