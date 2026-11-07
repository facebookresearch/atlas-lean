# Mean curvature of a level set

Let $E$ be a finite-dimensional real inner product space,
$\rho : E \to \mathbb{R}$ and $p \in E$. Write $\nabla\rho(p)$ for the gradient of $\rho$ at $p$,
$D^2\rho(p)$ for the second derivative of $\rho$ at $p$ (a bilinear form on $E$), and
$\Delta\rho(p) = \sum_i D^2\rho(p)(e_i, e_i)$ for a fixed orthonormal basis $(e_i)$ of $E$. The
mean curvature at $p$ of the level set of $\rho$ through $p$, with respect to the unit normal
$\nu = \nabla\rho(p) / \|\nabla\rho(p)\|$, is
$H = (\Delta\rho(p) - D^2\rho(p)(\nu, \nu)) / \|\nabla\rho(p)\|$, and $H = 0$ when
$\nabla\rho(p) = 0$.

This is the trace of the second fundamental form on the tangent hyperplane $\nabla\rho(p)^\perp$,
the sum of the principal curvatures, and it equals
$\operatorname{div}(\nabla\rho / \|\nabla\rho\|)(p)$ when $\rho$ is $C^2$ near $p$ and
$\nabla\rho(p) \neq 0$. Since $D^2\rho(p)$ is bilinear, $\Delta\rho(p)$ does not depend on the
choice of orthonormal basis.
