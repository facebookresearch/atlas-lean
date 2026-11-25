# Frisch–Waugh–Lovell, block form

Let $m$, $\kappa$, $\pi$ be finite index sets, let $W \in \mathbb{R}^{m \times m}$ be symmetric ($W^{\mathsf{T}} = W$), and let $A \in \mathbb{R}^{m \times \kappa}$, $Z \in \mathbb{R}^{m \times \pi}$, $y \in \mathbb{R}^m$, $b \in \mathbb{R}^{\kappa}$, $g \in \mathbb{R}^{\pi}$ and $U \in \mathbb{R}^{\kappa \times \pi}$. Suppose $(b, g)$ solves the weighted normal equations of the regression of $y$ on $[A \mid Z]$,

$$A^{\mathsf{T}} W (y - A b - Z g) = 0, \qquad Z^{\mathsf{T}} W (y - A b - Z g) = 0,$$

and that $Z_\perp = Z - A U$ is a weighted residual of $Z$ on $A$, that is $A^{\mathsf{T}} W Z_\perp = 0$. Then

$$(Z_\perp^{\mathsf{T}} W Z_\perp)\, g = Z_\perp^{\mathsf{T}} W y.$$

No positivity of $W$, rank condition or uniqueness of solutions is assumed.
