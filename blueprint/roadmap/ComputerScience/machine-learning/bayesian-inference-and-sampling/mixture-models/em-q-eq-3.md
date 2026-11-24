# The EM objective of a full-covariance Gaussian mixture splits by component

Let
$x_1, \dots, x_N$ be points of $\mathbb{R}^d$, and let $\theta'$ and $\theta$ be valid parameters
of a $K$-component full-covariance Gaussian mixture, where $\theta'$ has weights $\pi_k'$, means
$\mu_k'$ and covariance matrices $\Sigma_k'$. Then the EM objective of the mixture's joint density
satisfies

$$
Q(\theta' \mid \theta) = \sum_k \bigl(N_k \log \pi_k' + C_k(\mu_k', \Sigma_k')\bigr),
$$

where $r_{nk}$ is the responsibility of component $k$ for $x_n$ under $\theta$,
$N_k = \sum_n r_{nk}$ and $C_k(\mu, S) = \sum_n r_{nk} \log \mathcal{N}(x_n \mid \mu, S)$, with
$\mathcal{N}(\cdot \mid \mu, S)$ the multivariate Gaussian density with mean $\mu$ and covariance
matrix $S$.
