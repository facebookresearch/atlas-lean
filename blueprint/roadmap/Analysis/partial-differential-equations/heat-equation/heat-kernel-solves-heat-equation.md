# The Gaussian heat kernel solves the heat equation

Let $f\colon \mathbb{R} \to \mathbb{R}$
be continuous and bounded, and let $u(t, x)$ be the heat solution of $f$. Then for every
$t > 0$ and every $x \in \mathbb{R}$ there are a function $u_x\colon \mathbb{R} \to \mathbb{R}$
and a real number $u_{xx}$ such that $u(t, \cdot)$ has derivative $u_x(y)$ at every
$y \in \mathbb{R}$, $u_x$ has derivative $u_{xx}$ at $x$, and $u(\cdot, x)$ has derivative
$u_{xx}$ at $t$; that is, $\partial_t u = \partial_x^2 u$ on $(0, \infty) \times \mathbb{R}$.
Moreover, for every $x \in \mathbb{R}$, $u(t, x) \to f(x)$ as $t \to 0$ from above.

## Sources

- Classical heat-equation theory. Via leanprover/lean-eval@38361be, problem `heat_kernel_solves_heat_equation`.
