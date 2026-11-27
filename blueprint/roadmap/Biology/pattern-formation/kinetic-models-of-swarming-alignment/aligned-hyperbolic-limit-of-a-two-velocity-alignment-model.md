# Aligned hyperbolic limit of a two-velocity kinetic alignment model

**Model.** Let $f_j(t,x)\ge0$ be the density of entities at $x$ moving in direction $j\in\{-1,1\}$ with unit speed. Each entity reverses its orientation at a rate that increases with the local density of the opposite orientation, with *sensitivity* $\gamma > 0$:

$$\partial_tf_j + j\,\partial_xf_j = \frac{\mathbf 1\{f_j + f_{-j} > 0\}}{f_j^{\gamma} + f_{-j}^{\gamma}}\Big(f_{-j}f_j^{\gamma} - f_jf_{-j}^{\gamma}\Big), \qquad j = \pm1,$$

the diffusive limit of a discrete jump model in which a $j$-oriented entity turns with probability $\propto f_{-j}^\gamma/(f_j^\gamma + f_{-j}^\gamma)$ per step. For $\gamma = 1$ the equations decouple into free transport.

**Equilibria.** Spatially homogeneous equilibria with positive mass are either *isotropic* ($\bar f_1 = \bar f_{-1} > 0$) or *aligned* ($\bar f_j = 0 < \bar f_{-j}$). The total density $f_1 + f_{-1}$ is conserved by the space-homogeneous dynamics; for $\gamma > 1$ the majority orientation absorbs the whole mass (aligned equilibria attract), and for $0 < \gamma < 1$ the isotropic equilibrium attracts.

**Theorem (aligned picture, $\gamma > 1$).** Consider the hyperbolically scaled problem $\varepsilon(\partial_tf_j + j\partial_xf_j)$ equal to the right-hand side above on the torus $\mathbb T$ with continuous initial data $F = (F(1,\cdot),F(-1,\cdot))$ having continuous second derivatives, fix $k\in\{-1,1\}$, and assume $F(-k,x)\ge\mu > 0$ on $\mathbb T$. Let $h(\tau,x)$ be the *initial layer*, the solution of

$$\partial_\tau h = \frac{(\varrho_0 - h)h^{\gamma} - h(\varrho_0 - h)^{\gamma}}{(\varrho_0 - h)^{\gamma} + h^{\gamma}}, \qquad h(0,x) = F(-k,x), \qquad \varrho_0 = F(1,\cdot) + F(-1,\cdot).$$

For every $T > 0$ there are $\varepsilon_0 > 0$ and $c_\gamma > 0$ such that, if $\min_xF(k,x) \ge c_\gamma\max_xF(-k,x)$, then for $\varepsilon\in[0,\varepsilon_0)$ the Cauchy problem has a mild solution on $[0,T]$ and

$$\sup_{t\in[0,T]}\Big\|f(t) - \bar\varrho(t) - \bar h\big(\tfrac t\varepsilon\big)\Big\|_\infty \le c_T\,\varepsilon,$$

where $\bar\varrho(t,k,x) = \varrho_0(x - kt)$ with $\varrho_0 = F(1,\cdot) + F(-1,\cdot)$, $\bar\varrho(t,-k,x) = 0$ (all mass transported rigidly in direction $k$, a traveling wave) and $\bar h(\tau,k,\cdot) = -h(\tau,\cdot)$, $\bar h(\tau,-k,\cdot) = h(\tau,\cdot)$, with $h$ decaying exponentially in $\tau$ uniformly in $x$. (Theorem 5.2 of the source writes $\bar\varrho(t,k,x) = F(k,x-kt)$; then at $t = 0$ the $k$-component of the error is $F(-k,\cdot) \ge \mu > 0$, so the $c_T\varepsilon$ bound would fail. The layer equation already uses the total density $\varrho_0$.)

Near the isotropic equilibrium the corresponding parabolic scaling yields, at both zeroth and first order, the linear diffusion equation for the total density.

## Expansion

Writing $f_k = \bar\varrho - h + \varepsilon u$, $f_{-k} = h + \varepsilon v$ and expanding in $\varepsilon$, the fast time $\tau = t/\varepsilon$ governs the relaxation of the minority orientation through the homogeneous ODE for $h$ at fixed total density $\varrho_0$, while on the slow time scale the aligned majority is simply transported. For $\gamma > 1$ the minority fraction decays exponentially, and the dominance condition $\min F(k,\cdot) \ge c_\gamma\max F(-k,\cdot)$ makes the linearization of the layer equation in $x$-derivatives contractive, which controls $\partial_xh$. A Gronwall estimate on the remainder $(u,v)$ in the sup norm then gives the $O(\varepsilon)$ error on $[0,T]$.

## Sources

- Jacek Banasiak, Mirosław Lachowicz, "On a macroscopic limit of a kinetic model of alignment", arXiv (2012). Section 2 (model, equilibria), Theorem 3.1 (existence), Section 4 (formal macroscopic analysis, initial layer), Lemma 5.1, Theorem 5.2. <https://doi.org/10.48550/arXiv.1207.2643>. Published version: Mathematical Models and Methods in Applied Sciences 23(14) (2013), 2647–2670, <https://doi.org/10.1142/s0218202513500425>; locators above refer to the arXiv version.
