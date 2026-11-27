# Fisher information is the second moment of the score

Let $(\mathcal{X}, \nu)$ be a measure space and $p : \mathbb{R} \times \mathcal{X} \to \mathbb{R}$, $(\theta, x) \mapsto p_\theta(x)$, a one-parameter family of densities, with [score](score.md) $s_\theta(x) = \partial_\theta \log p_\theta(x)$, Fisher information $I(\theta) = \int (\partial_\theta p_\theta)^2 / p_\theta \, d\nu$ and $P_\theta$ the measure with density $\max(p_\theta, 0)$ with respect to $\nu$. Let $\theta \in \mathbb{R}$ with $p_\theta(x) > 0$ for every $x$, $p_\theta$ measurable and $t \mapsto p_t(x)$ differentiable at $\theta$ for every $x$. Then

$$\int s_\theta^2 \, dP_\theta = I(\theta).$$
