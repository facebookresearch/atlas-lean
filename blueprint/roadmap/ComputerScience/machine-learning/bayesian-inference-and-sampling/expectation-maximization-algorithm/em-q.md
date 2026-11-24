# The EM objective

Let $Z$ be a finite set, let $p_\theta(x, z)$ be real numbers indexed by
parameters $\theta$, observations $x$ and latent values $z \in Z$, let $x_1, \dots, x_N$ be data,
and write $p_\theta(z \mid x) = p_\theta(x, z) / \sum_{z' \in Z} p_\theta(x, z')$ for the posterior.
For parameters $\theta'$ and $\theta$, the EM objective is
$Q(\theta' \mid \theta) = \sum_{n=1}^N \sum_{z \in Z} p_\theta(z \mid x_n) \log p_{\theta'}(x_n, z)$
(maximized over $\theta'$ in the M-step).
