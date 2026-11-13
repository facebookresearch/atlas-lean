# Responsibilities of a Bernoulli mixture

Let $\theta$ be valid parameters of a mixture of
$K$ products of $d$ Bernoulli distributions, and write $p_\theta(x, k)$ for the joint probability
of a binary vector $x \in \{0,1\}^d$ and a component $k < K$ under $\theta$. The responsibility of
$k$ for $x$ is the posterior probability $r_k(x) = p_\theta(x, k) / \sum_{k' < K} p_\theta(x, k')$.
Computing it is the E-step of EM.
