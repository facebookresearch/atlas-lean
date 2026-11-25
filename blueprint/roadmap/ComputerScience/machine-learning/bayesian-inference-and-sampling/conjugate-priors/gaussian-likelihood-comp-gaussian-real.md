# The marginal of the data

Let $m_0 \in \mathbb{R}$ and $v_0, v > 0$, and write
$N(\mu, s)$ for the Gaussian law with mean $\mu$ and variance $s$. If the parameter $\theta$ has
prior $N(m_0, v_0)$ and the observation given $\theta$ has law $N(\theta, v)$ (the Gaussian
likelihood with noise variance $v$), then the marginal law of the observation is $N(m_0, v_0 + v)$.

Applied with the posterior in place of the prior, this also gives the posterior predictive law.
