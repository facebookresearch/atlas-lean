# Evidence lower bound of a single observation

Let $Z$ be a finite set, let
$p : Z \to \mathbb{R}$ give the joint values $p(z) = p(x, z)$ of a fixed observation $x$ with each
latent value $z \in Z$, and let $q : Z \to \mathbb{R}$. The evidence lower bound of $q$ is
$\mathrm{ELBO}(p, q) = \sum_{z \in Z} q(z) \bigl(\log p(z) - \log q(z)\bigr)$.
