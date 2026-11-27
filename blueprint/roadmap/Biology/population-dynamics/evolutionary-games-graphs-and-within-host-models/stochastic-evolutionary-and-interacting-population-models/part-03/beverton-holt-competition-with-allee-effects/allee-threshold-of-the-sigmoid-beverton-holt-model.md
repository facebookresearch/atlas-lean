# Allee threshold of the sigmoid Beverton–Holt model

The **sigmoid Beverton–Holt model** (a depensatory stock–recruitment map) is

$$u_{t+1} = H(u_t) = \frac{r\,u_t^{\delta}}{1 + u_t^{\delta}}, \qquad r,\delta > 0,\ u_0 > 0,$$

with per-capita growth $h(u) = r u^{\delta-1}/(1+u^\delta)$ and contest competition ($H(u)\to r > 0$ as $u\to\infty$). For $\delta > 1$ set

$$r_{\mathrm{crit}} = \delta\,(\delta - 1)^{\frac1\delta - 1}.$$

**Proposition.**

1. If $0 < \delta < 1$, there are two nonnegative equilibria: $0$, unstable, and a stable positive equilibrium $K$ (weak Allee effect).
2. If $\delta > 1$ and $r < r_{\mathrm{crit}}$, the only equilibrium is $0$, and it is locally stable.
3. If $\delta > 1$ and $r > r_{\mathrm{crit}}$ (strong Allee effect), there are three nonnegative equilibria $0 < A < K$ with $A < \frac{r(\delta-1)}{\delta} < K$: $0$ attracts $[0,A)$, the Allee threshold $A$ is a repeller, and the carrying capacity $K$ attracts $(A,\infty)$.

For the rescaled map $u_{t+1} = r u_t^\delta/(a + u_t^\delta)$ the same trichotomy holds with threshold $r^a_{\mathrm{crit}} = a^{1/\delta}\,\delta(\delta-1)^{\frac1\delta-1}$.

## Expansion

Positive fixed points solve $h(u) = 1$, i.e. $r u^{\delta-1} = 1 + u^\delta$. For $\delta > 1$ the function $\phi(u) = u^{\delta-1}/(1+u^\delta)$ vanishes at $0$ and $\infty$ and has a single maximum at $u^\ast = (\delta-1)^{1/\delta}$, with $\phi(u^\ast) = (\delta-1)^{1-1/\delta}/\delta = 1/r_{\mathrm{crit}}$. Hence there are no positive fixed points if $r < r_{\mathrm{crit}}$ and two, $A < u^\ast < K$, if $r > r_{\mathrm{crit}}$. Because $H$ is increasing, orbits are monotone and converge to fixed points; $H(u) < u$ on $(0,A)$ and $(K,\infty)$ and $H(u) > u$ on $(A,K)$, which gives the basins.

## Sources

- Yun Kang, "Dynamics of a generalized Beverton–Holt competition model subject to Allee effects", arXiv (2015). Section 2.1, Proposition 2.1 and Corollary 2.1. <https://doi.org/10.48550/arXiv.1505.05913>. Published version: "Dynamics of a generalized Ricker–Beverton–Holt competition model subject to Allee effects", Journal of Difference Equations and Applications 22(5) (2016), 687–723, <https://doi.org/10.1080/10236198.2015.1135910>; locators above refer to the arXiv version.
