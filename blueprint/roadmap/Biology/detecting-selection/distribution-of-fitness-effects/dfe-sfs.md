# Site-frequency spectrum under a distribution of fitness effects

For a measure $\mu$ on $\mathbb{R}$ (a distribution of the scaled selection coefficient $\sigma = 2Ns$), a real $\theta$ and natural numbers $n, i$, the expected spectrum is

$$\mathbb{E}\xi^\mu_i = \int \mathbb{E}\xi_i(\theta, \sigma) \, d\mu(\sigma),$$

where $\mathbb{E}\xi_i(\theta, \sigma)$ is the expected single-$\sigma$ Poisson-random-field spectrum (see the [uniform bound](abs-expected-sfs-le.md)), with the convention that the integral of a non-integrable function is $0$. When $\mu$ is a probability measure and $\theta \ge 0$, it is the expected number of sites with $i$ derived copies among $n$, for $1 \le i < n$, when each new mutation draws its own $\sigma$ from $\mu$.
