# Probabilistic PCA log-likelihood

For data $x_1, \dots, x_N \in \mathbb{R}^d$, a mean
$\mu \in \mathbb{R}^d$, a real $d \times q$ loading matrix $W$ and a real number $\sigma^2$, the
probabilistic PCA log-likelihood of the data is

$$
\sum_{n=1}^N \log \mathcal{N}(x_n \mid \mu, W W^\top + \sigma^2 I),
$$

where, for a real $d \times d$ matrix $\Sigma$ and $x \in \mathbb{R}^d$,

$$
\mathcal{N}(x \mid \mu, \Sigma) = (2\pi)^{-d/2} \bigl(\sqrt{\det \Sigma}\bigr)^{-1}
\exp\bigl(-\tfrac{1}{2} (x - \mu)^\top \Sigma^{-1} (x - \mu)\bigr)
$$

is the multivariate Gaussian density formula, read with the conventions $\sqrt{t} = 0$ for
$t < 0$, $0^{-1} = 0$, $\Sigma^{-1} = 0$ for singular $\Sigma$ and $\log 0 = 0$. These conventions
matter only when $W W^\top + \sigma^2 I$ is not positive definite. When $\sigma^2 > 0$ the matrix
$W W^\top + \sigma^2 I$ is positive definite, and this is the density of the Gaussian with mean
$\mu$ and covariance $W W^\top + \sigma^2 I$.
