# Equilibria, Hopf threshold and fear-driven finite-time extinction in a herd predator–prey model

**Model.** Prey density $u(t)$ and predator density $v(t)$ satisfy

$$\frac{du}{dt} = \frac{a u}{1 + k v} - b u^2 - c\,u^p v^m, \qquad \frac{dv}{dt} = -d v + e\,u^p v^m,$$

with $a, b, c, d, e > 0$, fear level $k \ge 0$ (predation risk lowers prey birth by the factor $1/(1+kv)$), prey herd behaviour exponent $0 < p < 1$ (only the herd boundary is exposed, so the functional response is $u^p$), and predator mutual-interference exponent $0 < m < 1$. Solutions started in the open quadrant stay non-negative and are uniformly bounded and dissipative.

**Theorem (coexistence equilibria).**
1. If $p + m \ge 1$ there is a unique coexistence equilibrium $E_2 = (u^*, v^*)$ with $u^*, v^* > 0$, and it is locally asymptotically stable (Routh–Hurwitz).
2. If $p + m < 1$ there are either no coexistence equilibria or exactly two, $E_2^1 = (u_1^*, v_1^*)$ and $E_2^2 = (u_2^*, v_2^*)$ with $0 < u_1^* < u_2^* < a/b$; in the latter case $E_2^1$ is a saddle and $E_2^2$ is locally asymptotically stable.

**Theorem (Hopf bifurcation in the fear level).** With $J$ the Jacobian at $E_2$, $S(k)$ its trace, $M(k)$ its determinant and $\eta_i(k)$ its eigenvalues, the system undergoes a Hopf bifurcation at $E_2$ when $k$ crosses

$$k_h = \frac{1}{v^*}\left[\frac{a}{2 b u^* + c p\,u^{*\,p-1} v^{*\,m} + d(1-m)} - 1\right],$$

provided $S(k_h) = 0$, $M(k_h) > 0$ and $\frac{d}{dk}\mathrm{Re}\,\eta_i(k)\big|_{k=k_h} \neq 0$. A saddle-node bifurcation of coexistence states occurs at a value $k_s$ where the slopes of the two nullclines coincide and $\operatorname{tr} J < 0$.

**Theorem (fear-driven finite-time extinction).** Fix parameters and an initial state $(u(0), v(0))$ whose trajectory converges to a stable coexistence equilibrium when $k = 0$. Then there is $k > 0$ such that the trajectory from the same initial state drives the prey to $0$ in finite time, after which the predator decays to $0$ asymptotically.

## Proof sketch

Because $p < 1$, the predation term $c u^p v^m$ is not Lipschitz at $u = 0$: near $u = 0$, $\dot u \approx -c\,v^m u^p$, whose solutions reach $0$ in finite time whenever the per-capita gain $a/(1+kv) - bu$ is too small to compensate. Raising $k$ shrinks prey reproduction without reducing predation pressure, which pushes the trajectory into this regime. Equilibrium counts follow from intersecting the monotone predator nullcline $e u^p v^{m-1} = d$ with the prey nullcline; the Hopf threshold is the value of $k$ at which the trace of $J$ vanishes with positive determinant.

## Sources

- Kwadwo Antwi-Fordjour, Rana D. Parshad, Hannah E. Thompson and Stephanie B. Westaway, "Fear-driven extinction and (de)stabilization in a predator-prey model incorporating prey herd behavior and mutual interference", *AIMS Mathematics* 8 (2023), 3353–3377, <https://doi.org/10.3934/math.2023173>. Preprint version: arXiv:2108.00546 (2021), model of Section 2, Lemmas 3.1–3.2, Theorems 3.3, 4.1, 4.2 and 5.1, <https://doi.org/10.48550/arXiv.2108.00546>.
