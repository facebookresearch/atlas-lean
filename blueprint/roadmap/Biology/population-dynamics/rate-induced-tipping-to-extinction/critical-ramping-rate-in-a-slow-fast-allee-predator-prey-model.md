# Critical ramping rate in a slow–fast Allee predator–prey model

**Model.** Prey $u$ (fast) with a strong Allee threshold $a \in (0,1)$ and inverse carrying capacity $\phi$, and predator $v$ (slow):
$$\varepsilon \dot u = u(1 - \phi u)(u - a) - uv, \qquad \dot v = v(u - 1), \qquad 0 < \varepsilon \ll 1 .$$
The environment degrades by ramping $\dot\phi = r$ for $\phi \in [\phi_{\min,\delta}, \phi_{\max,\delta})$ and $\dot\phi = 0$ otherwise, over a window of width of order $\delta$ above $\phi_{\min} = (2-a)^{-1}$.

**Theorem.**
1. The critical manifold $\{u(1-\phi u)(u-a) = uv\}$ consists of $S^0_0 = \{u = 0\}$ and the parabola-shaped $S^1_0 = \{v = (1 - \phi u)(u - a)\}$, folded where $1 + a\phi - 2\phi u = 0$. The reduced flow is $\dot v = -v$ on $S^0_0$ and
$$\dot u = (u - a)\,\frac{(1 - \phi u)(u - 1)}{1 + a\phi - 2\phi u} \quad \text{on } S^1_0 .$$
For fixed $\phi$, the extinction state is attracting on $S^0_0$, the prey-only state $u = 1/\phi$ attracts on $S^1_0$, the prey-only state $u = a$ repels, and the stability of the coexistence state $u = 1$ under the reduced flow changes with $\phi$ relative to $\phi_{\min}$.
2. With ramping, for small $r, \delta > 0$ the reduced flow on $S^1_0$ is $\dot u = (u - a)\frac{(1 - \phi u)(u - 1) + r u}{1 + a\phi - 2\phi u}$, $\dot\phi = r$, and there is a unique ecologically relevant folded saddle
$$FS_{\phi,r} = \Bigl(1 - \tfrac{2-a}{1-a} r + O(r^2),\ \tfrac{1}{2-a} + \tfrac{2}{(1-a)(2-a)} r + O(r^2)\Bigr)$$
whose strong canard separates trajectories that track the moving coexistence state from those that fall off the fold and tip to extinction.
3. There is a critical rate
$$r_{\mathrm{crit}} = \frac{(1-a)(2-a)}{2}\,\delta + \frac{(1-a)(2-a)^3}{2}\,\delta^2 + O(\delta^3)$$
such that for $r < r_{\mathrm{crit}}$ the population tracks the moving coexistence state, while for $r > r_{\mathrm{crit}}$ it tips to extinction.

## Expansion

The strong Allee effect makes extinction an attractor, so that, unlike earlier slow–fast predator–prey examples, populations that crash do not resurge. Ramping $\phi$ moves the coexistence state towards the fold of the critical manifold; tracking is possible only if the slow flow keeps the state on the attracting branch. Desingularising the reduced flow exposes the folded saddle, and the position of the initial condition relative to its strong canard decides the outcome; the canard's location depends on $r$, which gives the explicit critical rate. The model is minimal in that it combines the three ingredients needed for rate-induced extinction: slow–fast structure, bistability with an extinction attractor, and a folded critical manifold.

## Sources

- B. Hennessy, N. Popović, Z. Sattar, "A minimal model for rate-induced tipping to extinction", arXiv:2610.12319 (2026), Propositions 3, 4, 6, 7 and 8, Corollary 10, <https://doi.org/10.48550/arXiv.2610.12319>.
