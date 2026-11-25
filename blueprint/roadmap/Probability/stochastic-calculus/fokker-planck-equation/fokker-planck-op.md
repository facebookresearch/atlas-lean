# Fokker–Planck operator

For $D \in \mathbb{R}$, a drift $b$ and a density $p$ on $\mathbb{R}^n$, the Fokker–Planck operator is

$$(\mathcal L^* p)(x) = -\operatorname{div} J(x), \qquad J = b p - D \nabla p,$$

with $J$ the [probability flux](flux.md). The definition allows every real $D$. For $D \ge 0$, a
sufficiently regular density $p$ of the diffusion $dX = b\, dt + \sqrt{2D}\, dW$ evolves by
$\partial_t p = \mathcal L^* p$, and is stationary when $\mathcal L^* p = 0$.
