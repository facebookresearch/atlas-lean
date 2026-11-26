# Large-data global regularity of the three-dimensional chemotaxis–Stokes system with signal consumption

**Setting.** Consider the Cauchy problem in $\mathbb{R}^3$ for bacterial density $n$, oxygen concentration $c$ and fluid velocity $u$:

$$n_t + u\cdot\nabla n = \Delta n - \nabla\cdot(n\nabla c), \qquad c_t + u\cdot\nabla c = \Delta c - nc, \qquad u_t - \Delta u + \nabla\pi = nF,\ \ \nabla\cdot u = 0,$$

with a prescribed gravitational potential force $F = \nabla\Phi$.
Fix $0 < \beta < 1$ and assume $n_0, c_0 \in C_b^{2+\beta}(\mathbb{R}^3)$ are nonnegative,

$$M = \int_{\mathbb{R}^3} n_0 < \infty, \qquad \int_{\mathbb{R}^3} |x|^2 n_0 < \infty, \qquad 2\int_{\mathbb{R}^3}|\nabla\sqrt{c_0}|^2 < \infty,$$

and $u_0 \in H^4(\mathbb{R}^3)$ is divergence free, $F = \nabla\Phi \in W^{3,\infty}$. No smallness is imposed.

**Theorem.**
1. The system has a unique global classical solution in the class of bounded mild solutions (continuous in time with values in $(L^1\cap BUC)\times BUC^1\times(L^2\cap BUC)_\sigma$). For all $t \ge 0$, $n(t) \ge 0$, $0 \le c(t) \le \|c_0\|_\infty$ and $\int n(t) = M$, and for every finite $T$,

$$\sup_{0\le t\le T}\big(\|n(t)\|_\infty + \|c(t)\|_{W^{1,\infty}} + \|u(t)\|_2 + \|u(t)\|_\infty\big) < \infty.$$

2. *(Fluid-free case.)* Under the same hypotheses on $(n_0,c_0)$, the Keller–Segel consumption system $n_t = \Delta n - \nabla\cdot(n\nabla c)$, $c_t = \Delta c - nc$ in $\mathbb{R}^3$ has a unique global classical solution, bounded in $L^\infty\times W^{1,\infty}$ on every finite time interval.
3. *(Vanishing logistic damping.)* For the damped system with an extra $-\mu n^2$ in the density equation, for every $T$ there are $\mu_T > 0$ and $C_T$ such that, for $0 \le \mu \le \mu_T$, the damped solution exists on $[0,T]$ and differs from the undamped one by at most $C_T\mu$ in $L^\infty\times W^{1,\infty}$.

## Depends on

- [Local ε-regularity for the chemotaxis–Stokes system with signal consumption](local-epsilon-regularity-for-the-chemotaxis-stokes-system-with-consumption.md)

## Expansion

The classical energy $\int n\log n + \frac12\int|\nabla c|^2/c$ (the signal Fisher information) is dissipated but does not exclude concentration of $n$ in three dimensions. At a hypothetical first singular time, a terminal heat-kernel representation assigns a finite signal value to every point, and backward parabolic rescalings of $c$ converge strongly to it. Where the terminal signal is positive, a localized entropy estimate that stays uniform under density normalization shows that consumption ($-nc$) prevents normalized density concentration; where it is zero, a weighted localized estimate improves the integrability of $n$. Either way the scale-invariant density quantity decays, the ε-regularity criterion applies at every point, and a finite covering excludes a finite maximal time.

## Sources

- F. Shi, W. Wang and G. Yang, "Global regularity for the chemotaxis–Stokes system with signal consumption in $\mathbb{R}^3$", arXiv:2609.35204 (2026), Theorem 1.2, Corollaries 1.4 and 1.6, and Definition 1.1, proved in Sections 4–6, <https://doi.org/10.48550/arXiv.2609.35204>.
