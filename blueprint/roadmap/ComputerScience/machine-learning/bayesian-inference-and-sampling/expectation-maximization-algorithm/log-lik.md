# Log-likelihood of a latent-variable model

For a joint model $p$ with finite latent space
$Z$ and data $x_0, \dots, x_{N-1}$, the log-likelihood at the parameter $\theta$ is
$\ell(\theta) = \sum_{n < N} \log p_\theta(x_n)$, where
$p_\theta(x) = \sum_{z \in Z} p_\theta(x, z)$ is the marginal.
