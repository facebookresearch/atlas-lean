# Effective mortality threshold in a two-trait regulated mutation–selection model

**Model.** Individuals carry trait $0$ or $1$. Both give birth at per-capita rate $\lambda(1 - n/N)$, where $n = n_0 + n_1$ and $N$ is the ceiling; an offspring keeps its parent's trait with probability $q \in (0,1]$ and switches otherwise; trait-$i$ individuals die at rate $\mu_i$, with $\mu_1 \ge \mu_0$ (trait $0$ fitter). This is a continuous-time Markov chain on $\{n_0 + n_1 \le N\}$ absorbed at extinction. As $N \to \infty$ the densities $\mathbf{X}^N = \mathbf{n}/N$ converge in probability, uniformly on compact time intervals, to the solution of

$$\dot x_0 = \lambda(qx_0 + (1-q)x_1)(1 - m) - \mu_0x_0, \qquad \dot x_1 = \lambda((1-q)x_0 + qx_1)(1-m) - \mu_1x_1, \qquad m = x_0 + x_1,$$

and $N^{1/2}(\mathbf{X}^N - \mathbf{x})$ converges to a Gaussian diffusion (an Ornstein–Uhlenbeck process started at an equilibrium).

**Theorem (generic case $\mu_1 > \mu_0$, $q < 1$).** Let $s = \mu_0/\mu_1$, $\delta = q^2(1-s)^2 + 4(1-q)^2s$, and let

$$r^+ = \frac{-q(1-s) + \sqrt\delta}{2(1-q)} \in (0,1)$$

be the positive root of $(1-q)r^2 + q(1-s)r - (1-q)s = 0$. Define the *effective mortality*

$$\mu^* = \frac{\mu_0}{q + (1-q)r^+} = \frac{\mu_1 r^+}{1 - q + qr^+}, \qquad \mu_0 < \mu^* < \mu_1 .$$

- If $\lambda < \mu^*$, the origin is a stable node and the only equilibrium in the state space: the population dies out.
- If $\lambda > \mu^*$, the origin is a saddle and there is a unique interior equilibrium, a stable node,

$$x_0^* = \frac{m^*}{1 + r^+}, \qquad x_1^* = \frac{r^+m^*}{1 + r^+}, \qquad m^* = 1 - \frac{\mu^*}{\lambda},$$

with $x_1^* < x_0^*$; the trait ratio $r^+$ does not depend on $\lambda$.

**Special cases.** With no selection ($\mu_0 = \mu_1 = \mu$, $q < 1$), the interior equilibrium is $(\rho/2, \rho/2)$, $\rho = 1 - \mu/\lambda$, a stable node whenever $\lambda > \mu$, and the origin's eigenvalues are $\lambda(2q-1) - \mu$ and $\lambda - \mu$. With no mutation ($q = 1$), the equilibria are $0$, $(\rho_0, 0)$ (stable when $\lambda > \mu_0$ and $\mu_0 < \mu_1$) and $(0, \rho_1)$ (unstable), $\rho_i = 1 - \mu_i/\lambda$. When $q = 1/2$ the formula reduces to the harmonic mean $\mu^* = 2\mu_0\mu_1/(\mu_0 + \mu_1)$.

## Depends on

- [Spectral threshold for mutation–selection equilibrium on an infinite trait lattice](../mutation-selection-balance-on-infinite-trait-spaces/spectral-threshold-for-mutation-selection-equilibrium-on-the-integers.md)

## Expansion

Dividing the two equilibrium equations eliminates $1 - m$ and gives a quadratic for $r = x_1/x_0$; its positive root fixes the trait composition, and substituting back gives $\lambda(1-m)(q + (1-q)r) = \mu_0$, i.e. $m = 1 - \mu(r)/\lambda$. The trace and determinant of the Jacobian at $0$ and at $\mathbf{x}^*$ change sign exactly at $\lambda = \mu^*$ (the determinant at $\mathbf{x}^*$ is $\tfrac12(\mu_0 + \mu_1)(\lambda - \mu^*)$ in the $q = 1/2$ normalization), which gives the dichotomy. The same threshold structure, with $\mu^*$ replaced by a Perron eigenvalue condition, governs the infinite-trait version of the model.

## Sources

- P. Pollett, "Persistence, Thresholds, and Trait Composition in a Regulated Mutation-Selection Model", arXiv:2606.31146 (2026), Section 3 (no-selection, no-mutation and generic cases) and Appendix Theorems 1–3 and Corollary 1, <https://doi.org/10.48550/arXiv.2606.31146>.
