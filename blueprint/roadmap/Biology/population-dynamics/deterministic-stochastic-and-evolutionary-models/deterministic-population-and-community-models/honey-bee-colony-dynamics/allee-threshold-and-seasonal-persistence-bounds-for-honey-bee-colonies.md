# Allee threshold and seasonal persistence bounds for honey bee colony growth

**Model.** Let $u(t) \ge 0$ be the (rescaled) adult honey bee population of a colony. Brood survival requires enough adult bees to tend it, so recruitment is sigmoidal in $u$, while adults die at rate $\bar d_h > 0$:

$$u' = \frac{\bar r(t)\,u^2}{\hat K + u^2} - \bar d_h u, \qquad \bar r(t) = r_0\Big(1 + \epsilon\cos\frac{2\pi(t-\psi)}{\gamma}\Big),$$

with queen egg-laying rate $r_0 > 0$, seasonal intensity $\epsilon \in (0,1)$, season length $\gamma$, phase $\psi$ and half-saturation constant $\hat K > 0$. For a rate $r \ge 2\bar d_h\sqrt{\hat K}$ write

$$u_\pm(r) = \frac{r \pm \sqrt{r^2 - 4\bar d_h^2 \hat K}}{2\bar d_h}$$

for the roots of $\bar d_h u^2 - r u + \bar d_h \hat K = 0$.

**Proposition (constant egg laying, $\epsilon = 0$).** If $r_0 < 2\bar d_h\sqrt{\hat K}$ then $u(t) \to 0$ for every $u(0) \ge 0$. If $r_0 > 2\bar d_h\sqrt{\hat K}$ there are two positive equilibria $u_1^* = u_-(r_0) < u_2^* = u_+(r_0)$ and $u(t) \to 0$ if $u(0) < u_1^*$, $u(t) \to u_2^*$ if $u(0) > u_1^*$ (strong Allee effect).

**Theorem (seasonal egg laying).** Let $r_M = r_0(1+\epsilon)$ and $r_m = r_0(1-\epsilon)$.
1. If $r_M \le 2\bar d_h\sqrt{\hat K}$, then $u(t) \to 0$ for every $u(0) \ge 0$.
2. If $r_m \ge 2\bar d_h\sqrt{\hat K}$ and $u(0) > u_-(r_m)$, the colony persists with

$$u_-(r_m) < \liminf_{t\to\infty} u(t) \le \limsup_{t\to\infty} u(t) < u_+(r_M).$$

3. A positive $\gamma$-periodic solution $u^*$ is stable if $\int_0^\gamma \big[\bar r(z) f'(u^*(z)) - \bar d_h\big]dz < 0$ and unstable if this Floquet exponent is positive, where $f(u) = u^2/(\hat K + u^2)$ and $f'(u) = 2\hat K u/(\hat K + u^2)^2$. With a parasite (mite) population $v$ coupled through $-\frac{\omega u}{1+u}v$ in the bee equation and $v' = \frac{\omega u}{1+u}v - \bar d_m v$, the mite-free periodic solution $(u^*, 0)$ is stable if in addition $\int_0^\gamma \big[\frac{\omega u^*}{1+u^*} - \bar d_m\big]dt < 0$.

In terms of the seasonal intensity: if $r_0 < 2\bar d_h\sqrt{\hat K}$, the critical intensity $\epsilon_c = 2\bar d_h\sqrt{\hat K}/r_0 - 1 > 0$ marks the peak-rate threshold, since $\epsilon \le \epsilon_c$ is equivalent to $r_M \le 2\bar d_h\sqrt{\hat K}$, so for $\epsilon \le \epsilon_c$ the colony collapses from every initial population by item 1. If $r_0 > 2\bar d_h\sqrt{\hat K}$, the trough condition $r_m \ge 2\bar d_h\sqrt{\hat K}$ of item 2 is $\epsilon \le 1 - 2\bar d_h\sqrt{\hat K}/r_0$, and under it the colony persists from large initial populations. Outside these ranges, $r_m < 2\bar d_h\sqrt{\hat K} < r_M$, and neither item 1 nor item 2 applies; persistence then depends on season length and phase.

## Proof sketch

The per-capita growth $g(u) = \bar r u/(\hat K + u^2) - \bar d_h$ attains its maximum $\bar r/(2\sqrt{\hat K}) - \bar d_h$ at $u = \sqrt{\hat K}$, which gives the extinction threshold. Under seasonality the right-hand side is squeezed between the autonomous vector fields with rates $r_m$ and $r_M$, so comparison with their equilibria yields items 1–2. Item 3 is the linearisation of a scalar periodic equation along $u^*$; for the coupled system the mite-free cycle is triangular, so its Floquet exponents are the bee exponent and the mean mite growth rate along $u^*$.

## Sources

- Jun Chen, Jordy O. Rodriguez Rincon, Gloria DeGrandi-Hoffman, Jennifer Fewell, Jon Harrison and Yun Kang, "Impacts of seasonality and parasitism on honey bee population dynamics", *Journal of Mathematical Biology* 87 (2023), 19, <https://doi.org/10.1007/s00285-023-01952-2>. Preprint version: arXiv:2306.13300 (2023), Proposition 3.2, Theorems 3.3, 3.4 and 4.1, <https://doi.org/10.48550/arXiv.2306.13300>.
