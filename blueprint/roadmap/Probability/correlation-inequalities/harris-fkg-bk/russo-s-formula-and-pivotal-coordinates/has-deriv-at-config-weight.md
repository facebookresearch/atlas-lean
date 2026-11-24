# Derivative of the configuration weight

Let $E$ be a finite set and $\omega \in \{0,1\}^E$. For every $p \in \mathbb{R}$ the [product weight](config-weight.md) $p \mapsto W_p(\omega)$ is differentiable at $p$ with derivative (product rule)

$$\frac{d}{dp} W_p(\omega) = \sum_{e \in E} W_p^{(e)}(\omega)\, s_e(\omega), \qquad s_e(\omega) = \begin{cases} 1 & \omega(e) = 1, \\ -1 & \omega(e) = 0. \end{cases}$$
