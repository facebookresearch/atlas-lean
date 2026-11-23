# Covariance of the least-squares estimator

Let $X^\top X$ be invertible, and let the errors $\varepsilon_i$ be square-integrable, pairwise
uncorrelated, and of common variance $\sigma^2$: $\mathrm{Cov}(\varepsilon_i, \varepsilon_j)$ is
$\sigma^2$ if $i = j$ and $0$ otherwise. Then the least-squares estimate of $\beta$ in
$y = X\beta + \varepsilon$ satisfies

$$\mathrm{Cov}(\hat\beta_a, \hat\beta_b) = \sigma^2 \bigl((X^\top X)^{-1}\bigr)_{ab}.$$

No mean-zero or Gaussian hypothesis is needed.
