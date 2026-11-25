# The EM evidence lower bound is a sum of per-point ELBOs

Let $Z$ be a finite set, let
$p_\theta(x, z)$ be real numbers indexed by parameters $\theta$, observations $x$ and latent values
$z \in Z$, let $x_1, \dots, x_N$ be data, let $\theta$ be a parameter and let
$q_1, \dots, q_N : Z \to \mathbb{R}$. Then the evidence lower bound of expectation-maximization,
$\sum_{n=1}^N \sum_{z \in Z} q_n(z) \bigl(\log p_\theta(x_n, z) - \log q_n(z)\bigr)$, equals
$\sum_{n=1}^N \mathrm{ELBO}(p_\theta(x_n, \cdot), q_n)$, the sum over the data points of the
single-observation evidence lower bound of $q_n$ for the joint values
$z \mapsto p_\theta(x_n, z)$.
