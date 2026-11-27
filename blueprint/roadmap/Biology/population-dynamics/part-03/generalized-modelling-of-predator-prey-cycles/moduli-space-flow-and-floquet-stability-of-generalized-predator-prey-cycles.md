# Moduli-space flow and Floquet stability of generalized predator–prey cycles

**Generalized model.** Consider a planar predator–prey system with unspecified functional forms,

$$X' = S(X) - G(X,Y), \qquad Y' = G(X,Y) - M(Y), \qquad X, Y > 0,$$

where $S$ is prey production, $G$ predation and $M$ predator mortality. Suppose it has a $T$-periodic orbit $\gamma(t) = (\gamma_1(t), \gamma_2(t))$ (a predator–prey cycle). Normalizing $x = X/\gamma_1$, $y = Y/\gamma_2$ maps the cycle to $(1,1)$, and the system becomes

$$x' = \beta_s[s(x) - x] - \beta_1[g(x,y) - x], \qquad y' = \beta_2[g(x,y) - y] - \beta_m[m(y) - y],$$

with $T$-periodic **scale functions** $\beta_s = S(\gamma_1)/\gamma_1$, $\beta_1 = G(\gamma)/\gamma_1$, $\beta_2 = G(\gamma)/\gamma_2$, $\beta_m = M(\gamma_2)/\gamma_2$, and $T$-periodic **elasticity functions** $s_x = \gamma_1S'(\gamma_1)/S(\gamma_1)$, $g_x = \partial_x g(1,1)$, $g_y = \partial_y g(1,1)$, $m_y = \partial_y m(1)$. These generalize the scale and elasticity parameters of generalized modelling at equilibria to non-equilibrium (periodic) dynamics.

**Theorem.**

1. (Moduli-space flow.) Given elasticity functions $s_x, m_y, g_x, g_y$, the scale functions of any generalized model with a periodic orbit must satisfy

$$\begin{aligned} \beta_s' &= \beta_s(\beta_s - \beta_1)(s_x - 1),\\ \beta_m' &= \beta_m(\beta_2 - \beta_m)(m_y - 1),\\ \beta_1' &= \beta_1\bigl((\beta_s - \beta_1)g_x - (\beta_s - \beta_1) + (\beta_2 - \beta_m)g_y\bigr),\\ \beta_2' &= \beta_2\bigl((\beta_2 - \beta_m)g_y - (\beta_2 - \beta_m) + (\beta_s - \beta_1)g_x\bigr). \end{aligned}$$

2. (Obstruction.) If the elasticities are $T$-periodic with minimal period $T$ and this flow has no $T$-periodic solution, then no predator–prey model of the above form has a $T$-periodic orbit with these elasticities. In Fourier space, periodic scale functions must solve an explicit infinite system of convolution equations, for example $\frac{2\pi ik}{T}\hat\beta_s(k) = \hat\beta_s * (\hat\beta_s - \hat\beta_1) * (\hat s_x - \hat 1)$.

3. (Floquet multiplier.) For the cycle, the nontrivial Floquet multiplier is

$$\lambda = \exp\Bigl(\int_0^T \beta_s(s_x - 1) - \beta_1(g_x - 1) + \beta_2(g_y - 1) - \beta_m(m_y - 1)\,dt\Bigr).$$

When predation is linear in predators and mortality is linear ($g_y = m_y = 1$), this reduces to

$$\lambda = \exp\bigl(T(C_1 - C_2)\bigr), \qquad C_1 = \hat\beta_s * (\hat s_x - \hat 1), \quad C_2 = \hat\beta_1 * (\hat g_x - \hat 1).$$

So the cycle is stable ($|\lambda| < 1$) if and only if $C_2 > C_1$. Here $C_1 = \hat\beta_s(0)(\hat s_x(0) - 1) + 2\sum_{k\ge1}\bigl(\mathrm{Re}\,\hat\beta_s(k)\,\mathrm{Re}\,\hat s_x(k) + \mathrm{Im}\,\hat\beta_s(k)\,\mathrm{Im}\,\hat s_x(k)\bigr)$, and $C_2$ is analogous with $\hat\beta_1, \hat g_x$.

Stability of predator–prey cycles thus depends only on time-averaged correlations between scale functions and elasticities, not on the precise functional forms.

## Expansion

The flow in item 1 comes from differentiating the definitions of the scale functions along the orbit. For example, $\beta_s = S(\gamma_1)/\gamma_1$ gives $\beta_s' = \bigl(S'(\gamma_1) - S(\gamma_1)/\gamma_1\bigr)\gamma_1'/\gamma_1 = \beta_s(s_x - 1)\gamma_1'/\gamma_1$, and $\gamma_1'/\gamma_1 = \beta_s - \beta_1$ by the equation for $X$. Linearizing the normalized system at $(1,1)$ gives a periodic matrix $A(t)$. By Liouville's formula, its monodromy has determinant $\exp\int_0^T\operatorname{tr}A$. One multiplier is the trivial one along the flow, so the other equals this determinant. With $g_y = m_y = 1$ only the prey terms remain, and Parseval's identity turns the time average of products into the zeroth Fourier coefficient of convolutions.

## Sources

- Christian Kuehn, Thilo Gross, "Nonlocal Generalized Models of Predator-Prey Systems", arXiv (2011). Section 3 (non-equilibrium normalization, scale and elasticity functions, Floquet multiplier formula), Section 4 (Proposition 4.1, Theorem 4.2, Corollary 4.3), Section 6 (Proposition 6.1), Section 7 (Theorem 7.1, Proposition 7.2). <https://doi.org/10.48550/arXiv.1105.3662>. Published version: Discrete and Continuous Dynamical Systems - B 18(3) (2013), 693–720, <https://doi.org/10.3934/dcdsb.2013.18.693>; locators above refer to the arXiv version.
