# Non-equilibrium potential of one-species birth–death reaction networks

**Setting.** Let a reaction network have a single species $S$, with every reaction of the form $nS \to (n+1)S$ (rate constant $\kappa_n$, $n \ge 0$) or $nS \to (n-1)S$ (rate constant $\kappa_{-n}$), and at least one reaction of each kind. For a volume parameter $V > 0$, scale the rate constants as $\kappa^V_k = \kappa_k / V^{|\nu_k| - 1}$, where $|\nu_k|$ is the source molecularity, and use stochastic mass-action intensities $\lambda^V_k(x) = \kappa^V_k\, x!/(x - |\nu_k|)!$. The count process is then a birth–death chain with birth rates $p_i = \sum_{n \ge 0}\lambda^V_n(i)$ and death rates $q_i = \sum_{n < 0}\lambda^V_n(i)$. If needed, modify it so that its lowest reachable state $i_0$ is not absorbing. Let $n_u$ be the largest $n$ with $\kappa_n > 0$ and $n_d$ the largest $n$ with $\kappa_{-n} > 0$. For a positive stationary distribution $\pi$, its non-equilibrium potential is $-\ln\pi$.

**Theorem.** A stationary distribution $\pi^V$ exists on $\{i \ge i_0\}$ (for every $V > 0$) if

$$\text{(1)}\ \ n_d > n_u, \qquad\text{or}\qquad \text{(2)}\ \ n_d = n_u \text{ and } \kappa_{-n_d} > \kappa_{n_u}.$$

The conditions are sufficient but not necessary: when $n_d = n_u$ and $\kappa_{-n_d} = \kappa_{n_u}$, existence depends on lower-order terms (for $2S \to 3S$ and $2S \to S$, both with rate constant $1$, $\pi(x) \propto 2/(x(x-1))$ is summable). Under (1) or (2), let $\tilde\pi^V(\tilde x) = \pi^V(V\tilde x)$ on $V^{-1}\mathbb Z_{\ge 0}$. For every sequence $\tilde x^V \to \tilde x \in (0, \infty)$,

$$\lim_{V\to\infty} -\frac1V\ln\tilde\pi^V(\tilde x^V) = g(\tilde x) = -\int_{\tilde x_{\max}}^{\tilde x}\ln\Big(\frac{\sum_{n\ge0}\kappa_n u^{n}}{\sum_{n<0}\kappa_n u^{|n|}}\Big)\, du,$$

where $\tilde x_{\max}$ maximises $\int_0^{\tilde x}\ln(\cdot)\, du$ over $[0,\infty)$. Moreover $g$ decreases along trajectories of the deterministic mass-action ODE $\dot x = \sum_{n\ge0}\kappa_n x^n - \sum_{n<0}\kappa_n x^{|n|}$, so the scaled non-equilibrium potential converges to a Lyapunov-type function even when the network is not complex balanced.

**Example.** For $\emptyset \rightleftarrows X$, $2X \rightleftarrows 3X$ (rate constants $\kappa_0, \kappa_{-1}, \kappa_2, \kappa_{-3}$), condition (1) holds ($n_u = 2 < n_d = 3$) and

$$g(\tilde x) = -\int_{\tilde x_{\max}}^{\tilde x}\ln\frac{\kappa_0 + \kappa_2 x^2}{\kappa_{-1}x + \kappa_{-3}x^3}\, dx,$$

whose minima are the stable equilibria of the bistable ODE.

## Proof sketch

An irreducible birth–death chain has the explicit stationary law $\pi^V(x) \propto \prod_{i=i_0+1}^{x} p_{i-1}/q_i$. It is normalisable exactly when the products are summable. For large $i$ the ratio $p_{i-1}/q_i$ behaves like $(\kappa_{n_u}/\kappa_{-n_d})\, V^{n_d-n_u}\, i^{n_u - n_d}$, so under (1) or (2) the products decay faster than geometrically or geometrically, and are summable. With $x = V\tilde x$, the scaled ratio $p_{i-1}/q_i$ at $i = Vu$ tends to $\sum_{n\ge0}\kappa_n u^n / \sum_{n<0}\kappa_n u^{|n|}$. So $\frac1V\ln$ of the product is a Riemann sum converging to $\int_0^{\tilde x}\ln(\cdot)\,du$. The normalising constant contributes the maximum of this integral, by a Laplace argument. The Lyapunov property holds because $g'(x)$ and $\dot x$ have opposite signs: $g' = -\ln(\text{birth}/\text{death})$, while $\dot x = \text{birth} - \text{death}$.

## Sources

- David F. Anderson, Gheorghe Craciun, Manoj Gopalkrishnan and Carsten Wiuf, "Lyapunov Functions, Stationary Distributions, and Non-equilibrium Potential for Reaction Networks", *Bulletin of Mathematical Biology* 77 (2015), 1744–1767, <https://doi.org/10.1007/s11538-015-0102-8>. Preprint version: arXiv:1410.4820 (2014), Definitions 1 and 5, Section 4.1, Theorem 9 and Example 10, <https://doi.org/10.48550/arXiv.1410.4820>.
