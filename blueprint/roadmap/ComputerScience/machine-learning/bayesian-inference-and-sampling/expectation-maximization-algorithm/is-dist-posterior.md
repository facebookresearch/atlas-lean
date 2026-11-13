# Posteriors are probability distributions

Let $Z$ be a nonempty finite set and let
$p_\theta(x, z)$ be real numbers indexed by parameters $\theta$, observations $x$ and latent values
$z \in Z$, with $p_\theta(x, z) > 0$ for all $\theta$, $x$, $z$. For every parameter $\theta$ and
observation $x$, the posterior $z \mapsto p_\theta(x, z) / \sum_{z' \in Z} p_\theta(x, z')$ is a
probability distribution on $Z$: its values are nonnegative and sum to $1$.
