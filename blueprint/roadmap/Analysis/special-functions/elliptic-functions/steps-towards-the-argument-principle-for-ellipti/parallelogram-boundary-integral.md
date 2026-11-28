# Boundary integral over a parallelogram

For $g : \mathbb{C} \to \mathbb{C}$ and
$z_0, \omega_1, \omega_2 \in \mathbb{C}$, this is the integral of $g$ along the boundary of the
parallelogram with vertices $z_0$, $z_0 + \omega_1$, $z_0 + \omega_1 + \omega_2$, $z_0 + \omega_2$,
traversed in this order, with each side parametrized affinely by $t \in [0, 1]$:

$$\int_0^1 g(z_0 + t\omega_1)\,\omega_1\,dt +
\int_0^1 g(z_0 + \omega_1 + t\omega_2)\,\omega_2\,dt -
\int_0^1 g(z_0 + \omega_2 + t\omega_1)\,\omega_1\,dt -
\int_0^1 g(z_0 + t\omega_2)\,\omega_2\,dt.$$

Each integral is a Bochner interval integral, which is $0$ when the integrand is not integrable.
No relation between $\omega_1$ and $\omega_2$ is assumed; when
$\operatorname{Im}(\omega_2 / \omega_1) > 0$ the boundary is traversed counterclockwise.
