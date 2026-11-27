# Equilibria and bifurcations of the Lotka–Volterra competition model with Allee and fear effects

**Model.** Two competitors $x$ (subject to a strong Allee effect and to fear of its competitor) and $y$ (logistic) evolve, after nondimensionalization, by

$$\frac{dx}{dt} = x\Big[(1-x)(x-p)\frac{1}{1+qy} - a y\Big],\qquad \frac{dy}{dt} = b\,y\,(1 - y - c x),$$

with all parameters positive, Allee threshold $0 < p < 1$, fear coefficient $q > 0$, and initial data $x(0) > 0$, $y(0) > 0$.

**Basic properties.** Solutions stay positive and bounded, with $\limsup_{t\to\infty} y(t) \le 1$ and $x(t) \le \max\{x(0), 1\}$. If $0 < x(0) \le p$, $y(0) \ge 0$ and $(x(0), y(0)) \ne (p, 0)$, then $x(t) \to 0$, and $(x(t), y(t)) \to (0,1) = E_3$ if $y(0) > 0$, $(x(t), y(t)) \to (0,0) = E_0$ if $y(0) = 0$: below the Allee threshold the first species collapses.

**Equilibria.** Besides $E_0 = (0,0)$, the boundary equilibria are $E_1 = (1,0)$, $E_2 = (p,0)$ and $E_3 = (0,1)$. Interior equilibria $(x_*, 1 - c x_*)$ have $x_*$ a root of

$$A_1 x^2 + A_2 x + A_3 = 0,\qquad A_1 = a c^2 q + 1,\quad A_2 = -(2acq + ac + p + 1),\quad A_3 = a + aq + p,$$

with discriminant $\Delta = A_2^2 - 4A_1A_3$. When $\Delta > 0$, $2A_1 + A_2 > 0$ and $0 < c < 1$ there are two interior equilibria $E_{1*}$ (smaller $x$) and $E_{2*}$; when $\Delta = 0$, $2A_1 + A_2 > 0$ and $0 < c < 1$ they merge into a single $E_{3*}$; in the remaining listed cases ($c = 1$, or $1 < c \le 1 + 1/q$ with $0 < p < 1/c$) there is exactly one interior equilibrium $E_{1*}$.

**Stability.**

- $E_1$ is a stable node if $c > 1$ and a saddle if $0 < c < 1$; at $c = 1$ it is an attracting saddle-node when $p \ne 1 - a$ and a nonhyperbolic saddle when $p = 1 - a$.
- $E_2$ is an unstable node if $0 < p < 1/c$, a saddle if $p > 1/c$, and a repelling saddle-node if $p = 1/c$.
- Interior equilibria: $E_{1*}$ is a saddle, $E_{2*}$ a stable node, $E_{3*}$ a saddle-node.

**Bifurcations.** At $c_{TR} = 1$ (with $p \ne 1 - a$) the system undergoes a transcritical bifurcation at $E_1$. With the fear coefficient as parameter, under $2A_1 + A_2 > 0$ and $0 < c < 1$, a saddle-node bifurcation occurs at $E_{3*}$ when

$$q = q_* = \frac{a^2c^2 + 2acp + 2ac + p^2 - 4a - 2p + 1}{4a\,(c^2p - cp - c + 1)},$$

the value where $\Delta = 0$: as $q$ crosses $q_*$ the number of interior equilibria changes between $0$ and $2$.

## Depends on

- [Logistic growth equation](../../../logistic-growth-equation/logistic.md)

## Expansion

Positivity follows from writing each component as its initial value times an exponential of an integral. Boundedness of $y$ comes from comparison with the logistic equation; for $x$, the vector field points left on $\{x = 1\}$ and to the right of it. Interior equilibria are intersections of the line $y = 1 - cx$ with the fear-modified Allee nullcline, which reduces to the stated quadratic; root location in $(0,1)$ with $1 - cx \in (0,1)$ gives the case split. Hyperbolic stability is read off the Jacobian; the nonhyperbolic cases at $c = 1$ and $p = 1/c$ use center-manifold normal forms, and the bifurcations are verified with Sotomayor's transversality conditions. Because the fear term multiplies only the Allee growth factor, raising $q$ shrinks the region where both interior equilibria exist, so fear can remove the coexistence state entirely.

## Sources

- Shangming Chen, Fengde Chen, Vaibhava Srivastava and Rana D. Parshad, "Dynamical analysis of a Lotka–Volterra competition model with both Allee and fear effects", International Journal of Biomathematics 17 (2023), 2350077, <https://doi.org/10.1142/s1793524523500778>; numbering as in arXiv:2303.04919: Propositions 2.1, 2.3 and 2.4, Theorems 3.1, 4.1, 4.2, 4.3, 5.1 and 5.2.
