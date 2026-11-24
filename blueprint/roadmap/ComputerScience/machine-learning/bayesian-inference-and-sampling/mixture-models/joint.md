# Joint distribution of the Bernoulli mixture

For valid parameters $\theta$ of a mixture of
$K$ products of $d$ Bernoulli distributions, with mixing weights $\pi_k$ and success probabilities
$p_{kj}$, the joint probability of a binary vector $x \in \{0, 1\}^d$ and a component $k$ is

$$p_\theta(x, k) = \pi_k \prod_{j=1}^{d} p_{kj}^{x_j} (1 - p_{kj})^{1 - x_j},$$

that is, $\pi_k$ times the product Bernoulli probability of $x$ with parameters
$p_{k1}, \dots, p_{kd}$.
