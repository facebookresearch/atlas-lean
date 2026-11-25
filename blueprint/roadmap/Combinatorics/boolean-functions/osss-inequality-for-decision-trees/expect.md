# Expectation under a product weight

For a finite set $E$, weights $\nu = (\nu_e)_{e \in E}$ with $\nu_e : \{0, 1\} \to \mathbb{R}$ and $g : \{0, 1\}^E \to \mathbb{R}$, the expectation of $g$ under the product weight $\nu$ is

$$\mathbb{E}_\nu[g] = \sum_{\omega \in \{0, 1\}^E} \Big(\prod_{e \in E} \nu_e(\omega_e)\Big) g(\omega).$$

When $\nu$ is a [product probability weight](is-prob-weight.md) this is the expectation under the product measure with these one-coordinate marginals.
