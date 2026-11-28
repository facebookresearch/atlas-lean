# Zero growth rate at stationarity and the effect of environmental noise on mean population size

**Setting.** Populations follow a discrete-time random dynamical system $X_i(t+1) = X_i(t)\,f_i(\mathbf{X}(t), \mathbf{e}_t)$ on a state space $S \subset \mathbb{R}^n_{\ge0}$, where (A1) the environments $\mathbf{e}_t$ are i.i.d.; (A2) each per-capita fitness $f_i(\mathbf x, \mathbf e)$ is continuous in $\mathbf x$, jointly measurable and strictly positive; and (A3) the process returns to compact subsets of $S$ exponentially fast and the growth rates do not change too abruptly near infinity (for instance, all solutions eventually enter a fixed compact set and $\sup_{\mathbf x,\mathbf e}|\ln f_i(\mathbf x,\mathbf e)| < \infty$). For an invariant probability measure $\mu$, the per-capita (invasion) growth rate of species $i$ is $r_i(\mu) = \int \mathbb{E}[\ln f_i(\mathbf{x}, \mathbf{e}_1)]\,\mu(d\mathbf{x})$.

**Proposition (zero growth at stationarity).** For every invariant probability measure $\mu$ the rates $r_i(\mu)$ exist, and if $\mu$ is ergodic and species $i$ is present in the support of $\mu$, then $r_i(\mu) = 0$. If $\max_i r_i(\mu) > 0$ for every invariant measure $\mu$ supported on the extinction set (convex combinations included), the system is stochastically persistent, and under irreducibility it converges in total variation to a unique invariant measure $\pi$ on the coexistence set.

**Corollaries (single species, random carrying capacity $K_t$ i.i.d., $\bar K = \mathbb{E}K_1$).** Where $K_t$ is random, assume $K_1 > 0$ is nondegenerate (not almost surely constant), as the source does for its strict Jensen steps, and let $X_\infty$ denote the stationary population, independent of $K_1$. If $K_1 \equiv \bar K$ were constant, then $X_\infty = \bar K$ and each strict inequality below would fail (Beverton–Holt: all three members equal $\bar K$; Ricker: $1/\mathbb E(1/K_1) = \bar K$).
1. *Beverton–Holt*, $X_{t+1} = \frac{mK_t}{K_t + (m-1)X_t}X_t$, $m > 1$: $\mathbb{E}\ln(K_1 + (m-1)X_\infty) = \mathbb{E}\ln(mK_1)$, hence

$$\frac{e^{\mathbb{E}\ln(mK_1)} - \bar K}{m-1} \;<\; \mathbb{E}X_\infty \;<\; \bar K,$$

the upper bound being the Cushing–Henson inequality (noise is detrimental); the lower bound is positive iff $m\,e^{\mathbb{E}\ln K_1} > \mathbb{E}K_1$, which requires $m > \mathbb{E}K_1/(\mathbb{E}\sqrt{K_1})^2$ since $e^{\mathbb{E}\ln K_1} \le (\mathbb{E}\sqrt{K_1})^2$.
2. *Ricker*, $X_{t+1} = X_te^{r(1 - X_t/K_t)}$, $r > 1$: $\mathbb{E}X_\infty = 1/\mathbb{E}(1/K_1) < \bar K$, so noise in the carrying capacity always lowers the mean. If instead only the growth rate is random, $X_{t+1} = X_te^{r_t(1 - X_t/K)}$ with $\mathbb{E}r_1 \in (1,2)$, then $\mathbb{E}X_\infty = K$: the mean is unchanged.

**Theorem (small noise).** Write the dynamics as $\mathbf X(t+1) = \mathbf F(\mathbf X(t), \mathbf e_t)$ with the full map $F_i(\mathbf x, \mathbf e) = x_i f_i(\mathbf x, \mathbf e)$. Let $\mathbf{e}_t = \bar{\mathbf e} + \rho\,\xi_t$ with $\xi_t$ i.i.d. in a compact convex set and $\mathbb E\xi_t = 0$, and suppose the deterministic map $\mathbf F(\cdot, \bar{\mathbf e})$ has a globally attracting interior fixed point $\bar{\mathbf N}$ that is hyperbolic and linearly stable: the Jacobian $D_{\mathbf x}\mathbf F(\bar{\mathbf N}, \bar{\mathbf e})$ has spectral radius below $1$ (for one species, $|\partial F_1/\partial x_1| < 1$ at $(\bar N_1, \bar e)$). For small $\rho$, occupation measures converge a.s. to an invariant measure concentrated near $\bar{\mathbf N}$. For one species and one random coefficient, with derivatives of $F_1$ evaluated at $(\bar N_1, \bar e)$ and $\bar N_1^\rho$ distributed according to the invariant measure,

$$\mathbb{E}\bar N_1^\rho = \bar N_1 + \frac{b_1}{2}\Big(\frac{\partial^2 F_1}{\partial x_1^2}\tilde A_1 + \frac{\partial^2 F_1}{\partial \xi_1^2}\mathbb{E}\xi_1^2\Big)\rho^2 + O(\rho^3),$$

$$b_1 = \Big(1 - \frac{\partial F_1}{\partial x_1}\Big)^{-1}, \qquad \tilde A_1 = \Big(1 - \Big(\frac{\partial F_1}{\partial x_1}\Big)^2\Big)^{-1}\Big(\frac{\partial F_1}{\partial\xi_1}\Big)^2\mathbb{E}\xi_1^2,$$

so the sign of the $\rho^2$ correction, and hence whether noise raises or lowers the mean population, depends on the model and on which parameter fluctuates.

*Correction to the source.* The source's Theorem 4.1 and Corollary 4.1 print both second-order terms without the factor $\tfrac12$ and do not state $\mathbb E\xi = 0$; the formula above has both, matching the same authors' Theorem A.2 in "Population size in stochastic multi-patch ecological models" (2026). Example: $F(x,e) = (x + e^2)/2$, $e = 1 + \rho\xi$, $\xi = \pm1$ with equal probability. Then $\bar N = 1$, $b_1 = 2$, $\partial^2F/\partial x^2 = 0$, $\partial^2F/\partial\xi^2 = 1$, and stationarity gives $\mathbb E\bar N^\rho = \mathbb E e^2 = 1 + \rho^2$ exactly, as the corrected formula says; without the $\tfrac12$ one would get $1 + 2\rho^2$.

## Expansion

Ergodicity and the telescoping identity $\frac1t\ln X_i(t) = \frac1t\sum_{s<t}\ln F_i(\mathbf X(s), \mathbf e_s)$ force the long-run log growth rate of a species that is present at stationarity to be zero. Since $X_t$ is independent of $K_t$, the stationarity identity becomes an equation for moments of $X_\infty$: for Ricker, $\mathbb{E}[r(1 - X_\infty/K_1)] = 0$ gives $\mathbb{E}X_\infty\,\mathbb{E}(1/K_1) = 1$, and Jensen's inequality compares with $\bar K$; for Beverton–Holt, Jensen applied to $\ln$ gives the lower bound. The small-noise formula is a second-order Taylor expansion of the fixed-point equation around $\bar N$, with $\tilde A_1$ the leading variance of the stationary fluctuations of the linearized AR(1) recursion.

## Proof depends on

- [Small-noise approximation of stationary patch population size](../dispersal-and-environmental-stochasticity-in-patch-models/small-noise-approximation-of-stationary-patch-population-size.md)

## Sources

- A. Hening and S. Sabharwal, "Population size in stochastic discrete-time ecological dynamics", *Journal of Mathematical Biology* 91(4) (2025), 36, Proposition 2.1, Theorem 2.1, Section 2.1 (Assumptions (A1)–(A3)), Section 3, Theorem 4.1 and Corollary 4.1, <https://doi.org/10.1007/s00285-025-02277-y> (preprint arXiv:2507.09325).
- A. Hening, S. Sabharwal, "Population size in stochastic multi-patch ecological models", *Journal of Mathematical Biology* 92(3) (2026), 43, Theorem A.2 (the factor $\tfrac12$), <https://doi.org/10.1007/s00285-026-02365-7> (preprint arXiv:2511.19743).
