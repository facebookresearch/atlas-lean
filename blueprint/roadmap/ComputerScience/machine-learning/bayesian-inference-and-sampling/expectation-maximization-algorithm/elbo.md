# Evidence lower bound of latent distributions

Let $Z$ be a finite set, let
$p_\theta(x, z)$ be real numbers indexed by parameters $\theta$, observations $x$ and latent values
$z \in Z$, and let $x_1, \dots, x_N$ be data. For a parameter $\theta$ and functions
$q_1, \dots, q_N : Z \to \mathbb{R}$ (one latent distribution per data point), the evidence lower
bound is $\sum_{n=1}^N \sum_{z \in Z} q_n(z) \bigl(\log p_\theta(x_n, z) - \log q_n(z)\bigr)$.
