# For k > 0 the compliance derivative is −p times the tip displacement

For every stiffness $k > 0$ and every end force $F$, the [compliance](compliance.md) $J(F, \cdot)$
is differentiable at $k$, with

$$\frac{dJ}{dk} = -\,p\, u_{\mathrm{tip}}, \qquad p = u_{\mathrm{tip}} = \frac{F}{k},$$

minus the product of the [scalar adjoint](adjoint-displacement.md) and the
[tip displacement](tip-displacement.md), which [equals](neg-adjoint-displacement-mul-tip-displac.md)
$-F^2 / k^2 \le 0$. The derivative is a two-sided derivative on the open half-line $k > 0$, so it
also holds at an endpoint of a feasible interval contained in $(0, \infty)$.
