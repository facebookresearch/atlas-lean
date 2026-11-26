# Frisch–Waugh–Lovell, block solved form

Let $m$, $\kappa$, $\pi$ be finite index sets, let $W \in \mathbb{R}^{m \times m}$ be symmetric, and let $A \in \mathbb{R}^{m \times \kappa}$, $Z \in \mathbb{R}^{m \times \pi}$, $y \in \mathbb{R}^m$, $b, v \in \mathbb{R}^{\kappa}$, $g \in \mathbb{R}^{\pi}$ and $U \in \mathbb{R}^{\kappa \times \pi}$ satisfy

$$A^{\mathsf{T}} W (y - A b - Z g) = 0, \qquad Z^{\mathsf{T}} W (y - A b - Z g) = 0, \qquad A^{\mathsf{T}} W (Z - A U) = 0.$$

Write $Z_\perp = Z - A U$ and suppose the residualized Gram matrix $G = Z_\perp^{\mathsf{T}} W Z_\perp$ is nonsingular ($\det G \ne 0$). Then

$$g = G^{-1} Z_\perp^{\mathsf{T}} W (y - A v).$$
