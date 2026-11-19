# Marginal log-likelihood of the mean

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals with [phenotypic covariance](v.md) $V$. For a phenotype vector $y \in \mathbb{R}^n$ and a mean $\mu \in \mathbb{R}^n$, the marginal log-likelihood of $\mu$ is

$$\ell(\mu) = -\frac{1}{2}\Bigl(n \log(2\pi) + \log \det V + (y - \mu)^\top V^{-1} (y - \mu)\Bigr),$$

the logarithm of the density of $N(\mu, V)$ at $y$ (here $\det V > 0$ because $V$ is positive definite).
