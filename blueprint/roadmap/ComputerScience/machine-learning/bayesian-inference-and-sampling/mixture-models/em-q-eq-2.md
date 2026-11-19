# The EM objective of an isotropic Gaussian mixture splits by component

Let
$x_1, \dots, x_N$ be points of $\mathbb{R}^d$, and let $\theta'$ and $\theta$ be valid parameters
of a $K$-component isotropic Gaussian mixture, where $\theta'$ has weights $\pi_k'$, means
$\mu_k'$ and variances $v_k'$. Then the EM objective of the mixture's joint density satisfies

$$
Q(\theta' \mid \theta) = \sum_k \bigl(N_k \log \pi_k' + C_k(\mu_k', v_k')\bigr),
$$

where $r_{nk}$ is the responsibility of component $k$ for $x_n$ under $\theta$,
$N_k = \sum_n r_{nk}$ and
$C_k(\mu, v) = \sum_n r_{nk} \bigl(-\tfrac{d}{2} \log(2\pi v) - \|x_n - \mu\|^2 / (2v)\bigr)$.
