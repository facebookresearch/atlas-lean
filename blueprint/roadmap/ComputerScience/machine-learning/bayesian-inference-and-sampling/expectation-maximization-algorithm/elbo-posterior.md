# The bound is tight at the posterior

Let $Z$ be a nonempty finite set, let
$p_\theta(x, z)$ be real numbers indexed by parameters $\theta$, observations $x$ and latent values
$z \in Z$, with $p_\theta(x, z) > 0$ for all $\theta$, $x$, $z$, and let $x_1, \dots, x_N$ be data.
For every parameter $\theta$, the posteriors
$q_n(z) = p_\theta(z \mid x_n) = p_\theta(x_n, z) / \sum_{z' \in Z} p_\theta(x_n, z')$ satisfy

$$
\sum_{n=1}^N \sum_{z \in Z} q_n(z) \bigl(\log p_\theta(x_n, z) - \log q_n(z)\bigr) =
\sum_{n=1}^N \log \sum_{z \in Z} p_\theta(x_n, z),
$$

that is, the evidence lower bound at $\theta$ of the posteriors equals the log-likelihood of the
data at $\theta$.
