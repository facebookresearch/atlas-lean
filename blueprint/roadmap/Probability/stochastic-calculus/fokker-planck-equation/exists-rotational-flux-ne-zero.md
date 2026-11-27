# An explicit rotational drift with nonzero flux

On $\mathbb{R}^2$ let $\Psi(x) = (x_0^2 + x_1^2)/2$, $D = 1$, and $A = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$. For the
drift $b = -(\nabla \Psi + A \nabla \Psi)$ and the [Gibbs density](gibbs.md) $p = e^{-\Psi}$ (the standard
Gaussian density up to normalisation), the [probability flux](flux.md) $J = b p - \nabla p$ satisfies
$\operatorname{div} J = 0$ everywhere, so $p$ is stationary, but $J(1, 0) \ne 0$: $b$ is not the gradient
drift $-\nabla \Psi$.
