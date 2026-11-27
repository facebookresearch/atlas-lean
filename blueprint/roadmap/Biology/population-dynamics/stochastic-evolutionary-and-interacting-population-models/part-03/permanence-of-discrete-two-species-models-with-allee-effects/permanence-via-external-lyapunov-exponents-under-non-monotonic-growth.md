# Permanence via external Lyapunov exponents under non-monotonic growth

Consider the discrete-time two-species model

$$x_{t+1} = x_t\, f(x_t, y_t), \qquad y_{t+1} = y_t\, g(x_t, y_t),$$

on $\mathbb R_+^2$, where the per capita growth rates $f, g$ are nonnegative and twice differentiable and may be non-monotonic in either density (as under Allee effects). Write $F = \ln f$, $G = \ln g$. Along an orbit $(x_i, 0)$ on the $x$-axis, the **external Lyapunov exponent** $\check r^{yx}(x_0,0) = \limsup_n \frac1n\sum_{i<n} \ln g(x_i,0)$ is the long-run invasion rate of a rare $y$ into the resident $x$ dynamics, and symmetrically for $x$ invading $y$. The system is **permanent** if there is a compact set in the open quadrant that absorbs every orbit starting with both species positive.

**Theorem (permanence criterion).** Suppose $f, g > 0$ off the origin with $f(0,0) > 1$, the single-species densities are eventually bounded, all nontrivial boundary fixed points are unsaturated ($f(0,y^*) > 1$ and $g(x^*,0) > 1$), and the external Lyapunov exponents of both boundary dynamics are positive in the sense of conditions G3–G4 of the source, which bound them below by $G(x^*,0) - G_x(x^*,0)F(x^*,0)/F_x(x^*,0)$ plus a nonnegative **relative nonlinearity** term built from second derivatives of $F$ and $G$. Then the system is permanent.

**Corollary (competition with weak Allee effects in both species).** For

$$x_{t+1} = x_t\exp\Big(r_1(1 - x_t) - \frac{m_1}{1 + b_1 x_t} - a_1 y_t\Big), \qquad y_{t+1} = y_t\exp\Big(r_2(1 - y_t) - \frac{m_2}{1 + b_2 y_t} - a_2 x_t\Big),$$

with all parameters positive, let $x^*, y^*$ be the positive single-species equilibria. The system is permanent if

1. $r_i > m_i$ for $i = 1,2$ (each species alone has only a weak Allee effect);
2. $F(0, y^*) > 0$ and $G(x^*, 0) > 0$ (each species can invade the other at equilibrium);
3. $r_2 > b_2 m_2/(1 + b_2 y^*)^2$ and $r_1 > b_1 m_1/(1 + b_1 x^*)^2$.

Here $x^* = \big(r_1(b_1 - 1) + \sqrt{r_1^2(1+b_1)^2 - 4 m_1 b_1 r_1}\big)/(2 r_1 b_1)$ and analogously for $y^*$.

## Expansion

Permanence follows from an average Lyapunov function $P(x,y) = x^{p_1}y^{p_2}$: it suffices that along every orbit in the boundary attractor the weighted time-average of $p_1 F + p_2 G$ is positive. On the $x$-axis, Taylor-expanding $G(x_i,0)$ and $F(x_i,0)$ around a reference point $x^*$ and using that the time-average of $F(x_i,0)$ vanishes for bounded orbits, the invasion exponent equals $G(x^*,0) - \frac{G_x}{F_x}F(x^*,0)$ plus an average of second-order remainders: the relative nonlinearity of $g$ with respect to $f$. When this term is nonnegative, invasion is guaranteed by a condition at a single point even if the resident dynamics are periodic or chaotic. In the Ricker example condition 3 makes the relevant second-order terms have the right sign, and condition 2 is the pointwise invasion condition.

## Sources

- Yun Kang, "Permanence of a general discrete-time two-species-interaction model with non-monotonic per capita growth rates", arXiv (2011). Section 2 (Condition H, Lemmas 2.1–2.2, Corollary 2.1, external Lyapunov exponents), Section 3 (Conditions G1–G4, Theorem 3.1, Corollary 3.1), Section 5.2 (weak Allee competition model and Corollary 5.2). <https://doi.org/10.48550/arXiv.1102.5563>. Published version: Discrete and Continuous Dynamical Systems - B 18(8) (2013), 2123–2142, <https://doi.org/10.3934/dcdsb.2013.18.2123>; locators above refer to the arXiv version.
