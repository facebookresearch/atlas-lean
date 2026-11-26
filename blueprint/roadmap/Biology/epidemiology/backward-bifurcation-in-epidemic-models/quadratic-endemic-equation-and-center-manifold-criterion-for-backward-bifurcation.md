# Quadratic endemic equation and center-manifold criterion for backward bifurcation

**Setting.** An epidemic model $\dot x = f(x, \phi)$ on $\mathbb{R}^n_{\ge 0}$ has a disease-free equilibrium $x_0$ for all values of a bifurcation parameter $\phi$ (usually a transmission rate), and a control reproduction number $R$ with $R = 1$ at $\phi = \phi^\ast$. The bifurcation at $R = 1$ is **forward** if endemic equilibria exist only for $R > 1$ and are small and stable near $R = 1$, and **backward** if, for some $R_c < R < 1$, two endemic equilibria (one stable, one unstable) coexist with the locally stable disease-free equilibrium.

**Proposition (quadratic endemic equation).** Suppose endemic equilibria are in bijection with positive roots $\lambda^\ast > 0$ (the equilibrium force of infection) of
$$a_1 \lambda^2 + a_2 \lambda + a_3 = 0, \qquad a_1 > 0, \qquad \operatorname{sign} a_3 = \operatorname{sign}(1 - R).$$
Then: if $R > 1$ ($a_3 < 0$) there is exactly one endemic equilibrium; if $R = 1$ ($a_3 = 0$) there is one when $a_2 < 0$ and none otherwise; if $R < 1$ ($a_3 > 0$) there are two when $a_2 < 0$ and $a_2^2 - 4a_1a_3 > 0$, and none otherwise. A backward bifurcation therefore occurs exactly when $a_2 < 0$ at $R = 1$, and the critical value $R_c$ below which no endemic equilibrium exists solves $a_2^2 = 4 a_1 a_3$.

**Theorem (Castillo-Chavez–Song).** Assume $f$ is $C^2$, the Jacobian $A = D_x f(x_0, \phi^\ast)$ has a simple zero eigenvalue and all other eigenvalues have negative real parts, with right and left null vectors $w$ and $v$ ($Aw = 0$, $v^\top A = 0$, $v^\top w = 1$). Let
$$a = \sum_{k,i,j} v_k\, w_i\, w_j\, \frac{\partial^2 f_k}{\partial x_i\, \partial x_j}(x_0, \phi^\ast), \qquad b = \sum_{k,i} v_k\, w_i\, \frac{\partial^2 f_k}{\partial x_i\, \partial \phi}(x_0, \phi^\ast).$$
If $b > 0$, then for $a < 0$ the bifurcation at $\phi = \phi^\ast$ is forward (a locally stable endemic equilibrium appears for $\phi > \phi^\ast$), and for $a > 0$ it is backward (a locally unstable endemic equilibrium exists for $\phi < \phi^\ast$ close to $\phi^\ast$).

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

For the quadratic, the product of the roots is $a_3/a_1$ and their sum is $-a_2/a_1$. When $a_3 < 0$ the roots have opposite signs, so exactly one is positive. When $a_3 > 0$ the roots have equal signs and are positive iff $a_2 < 0$ and they are real, i.e. the discriminant is nonnegative. In models with an imperfect (leaky) vaccine of efficacy $\theta \in (0,1)$, vaccinated individuals can still be infected, and the extra infection flux produces the negative $a_2$; with a perfect vaccine ($\theta = 1$) a linear Lyapunov function $L = p_1 E + p_2 A + p_3 I$ gives $\dot L \le c\,(R - 1)E$, so the disease-free equilibrium is globally stable for $R \le 1$ and no backward bifurcation can occur. The center-manifold theorem reduces the dynamics near $(x_0, \phi^\ast)$ to the scalar normal form $\dot c = a c^2 + b(\phi - \phi^\ast) c$ along the direction $w$, whose nonzero equilibrium $c = -b(\phi - \phi^\ast)/a$ is biologically relevant (positive) for $\phi > \phi^\ast$ when $a < 0$ and for $\phi < \phi^\ast$ when $a > 0$. Under a backward bifurcation, reducing $R$ just below $1$ does not guarantee elimination; $R$ must be pushed below $R_c$.

## Sources

- Z.-H. Shen, Y.-M. Chu, M. A. Khan, S. Muhammad, O. A. Al-Hartomy and M. Higazy, "Mathematical modeling and optimal control of the COVID-19 dynamics", Results in Physics 31 (2021), 105028, Vaccination model (Theorems 3–5), <https://doi.org/10.1016/j.rinp.2021.105028>, PMCID: PMC8627298.
- C. Castillo-Chavez and B. Song, "Dynamical models of tuberculosis and their applications", Mathematical Biosciences and Engineering 1 (2004), 361–404, Theorem 4.1, <https://doi.org/10.3934/mbe.2004.1.361>.
