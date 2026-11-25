# EM iterates have monotone likelihood

Let $Z$ be a nonempty finite set, let
$p_\theta(x, z)$ be real numbers indexed by parameters $\theta$, observations $x$ and latent values
$z \in Z$, with $p_\theta(x, z) > 0$ for all $\theta$, $x$, $z$, and let $x_1, \dots, x_N$ be data.
Write $p_\theta(z \mid x) = p_\theta(x, z) / \sum_{z' \in Z} p_\theta(x, z')$ for the posterior,
$Q(\theta' \mid \theta) = \sum_{n=1}^N \sum_{z \in Z} p_\theta(z \mid x_n) \log p_{\theta'}(x_n, z)$
for the EM objective and $\ell(\theta) = \sum_{n=1}^N \log \sum_{z \in Z} p_\theta(x_n, z)$ for the
log-likelihood. Let $M$ be a map on parameters, with $k$-th iterate $M^k$ ($M^0$ the identity),
such that $Q(M\theta \mid \theta) \ge Q(\theta \mid \theta)$ for every $\theta$ (in particular if
$M\theta$ maximizes $Q(\cdot \mid \theta)$, or $M$ is a generalized-EM step). Then for every
$\theta_0$ the sequence $k \mapsto \ell(M^k \theta_0)$ is nondecreasing.
