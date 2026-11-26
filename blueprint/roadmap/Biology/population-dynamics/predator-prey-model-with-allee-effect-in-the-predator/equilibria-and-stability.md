# Predator–prey model with an Allee effect in the predator: equilibria and stability

**Model.** In dimensionless form, prey $x \ge 0$ and predator $y \ge 0$ satisfy
$$\frac{dx}{dt} = x(1-x) - \frac{xy}{\beta + x}, \qquad \frac{dy}{dt} = \frac{\alpha xy}{\beta + x}\,h(y) - my,$$
with $\alpha, \beta, m > 0$ (Holling type II functional response) and an Allee-effect function $h$ that multiplies the predator's conversion efficiency and satisfies (A1) $h(0) = 0$; (A2) $0 \le h \le 1$; (A3) $h' > 0$; (A4) $h'' < 0$; (A5) $h(y) \to 1$ as $y \to \infty$. Examples: $h(y) = y/(\delta + y)$, $1 - e^{-y/\delta}$, $\tanh(y/\delta)$.

**Boundary equilibria (Proposition 1).** For every $h$ satisfying (A1)–(A5), $E_0 = (0,0)$ is a saddle (eigenvalues $1$ and $-m$) and the predator-free equilibrium $E_1 = (1,0)$ is locally asymptotically stable (eigenvalues $-1$ and $-m$). Thus predator extinction is always locally attracting: the Allee effect is strong.

**Interior equilibria.** Interior equilibria are intersections of the prey nullcline $y = (1-x)(\beta+x)$ with the predator nullcline $x = m\beta/(\alpha h(y) - m)$, which requires $\alpha > m$, $x^* > m\beta/(\alpha - m)$ and $y^* > h^{-1}(m/\alpha)$. The predator nullcline is strictly decreasing and convex as a function of $y$, so there are at most two interior equilibria $E_1^* = (x_1^*,y_1^*)$, $E_2^* = (x_2^*,y_2^*)$ with $0 < x_1^* < x_2^* < 1$. With $x_m = (1-\beta)/2$ the abscissa of the prey-nullcline maximum:

- $E_2^*$ is always a saddle;
- $E_1^*$ has positive Jacobian determinant (it is a node or focus); its stability is decided by $\operatorname{tr}J(E_1^*) = x_1^*f^1_x + y_1^*f^2_y$, where $f^1_x$ has the sign of $x_m - x_1^*$ and $f^2_y = \alpha x_1^*h'(y_1^*)/(\beta+x_1^*) > 0$; hence $E_1^*$ is unstable if $x_1^* < x_m$, and if $x_m < x_1^*$ it is locally asymptotically stable exactly when the trace is negative.

Without the Allee effect ($h \equiv 1$) there is at most one interior equilibrium, on the line $x = m\beta/(\alpha - m)$.

## Expansion

At an interior equilibrium write the Jacobian as $\begin{pmatrix} xf^1_x & xf^1_y\\ yf^2_x & yf^2_y\end{pmatrix}$ with $f^1 = 1 - x - y/(\beta+x)$, $f^2 = \alpha xh(y)/(\beta+x) - m$. Implicit differentiation gives $\det J = xyf^1_yf^2_y\big[(dy/dx)_{f^2} - (dy/dx)_{f^1}\big]$ with $f^1_y < 0 < f^2_y$, so the sign of the determinant is decided by which nullcline is steeper at the crossing; at the right intersection the predator nullcline is steeper (saddle), at the left one the prey nullcline is. On the prey nullcline $f^1_x = (1-\beta-2x)/(\beta+x)$, which is positive exactly left of $x_m$; with $f^2_y > 0$ this makes the trace positive there.

## Sources

- Deeptajyoti Sen, Saktipada Ghorai and Malay Banerjee, "Bifurcation analysis of the predator–prey model with the Allee effect in the predator", Journal of Mathematical Biology (2021), <https://doi.org/10.1007/s00285-021-01707-x> (PMC8718388). Section 2 (assumptions (A1)–(A5), model (2)); Section 3, Eqs. (3)–(14) and Proposition 1.
