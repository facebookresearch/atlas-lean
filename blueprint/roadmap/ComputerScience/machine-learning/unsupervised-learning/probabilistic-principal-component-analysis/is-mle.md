# Probabilistic PCA maximum-likelihood estimate

Given data
$x_1, \dots, x_N \in \mathbb{R}^d$, a triple $(\mu_0, W_0, \sigma_0^2)$ of a mean
$\mu_0 \in \mathbb{R}^d$, a real $d \times q$ loading matrix $W_0$ and a real number $\sigma_0^2$
is a probabilistic PCA maximum-likelihood estimate when $\sigma_0^2 > 0$ and, for every
$\mu \in \mathbb{R}^d$, every real $d \times q$ matrix $W$ and every real $\sigma^2 > 0$, the
probabilistic PCA log-likelihood of the data at $(\mu, W, \sigma^2)$ is at most its value at
$(\mu_0, W_0, \sigma_0^2)$.
