# Endemic concentration of noisy SIS and SIRS epidemics on totally mixing networks

**Setting.** Consider network SIS and SIRS epidemics as pairwise interaction network models on an asymptotically totally mixing (ATM) graph sequence $\mathcal{G}_n$, for example Erdős–Rényi graphs $\mathcal{G}(n,p_n)$ with $np_n \to \infty$. Without spontaneous infection the all-susceptible configuration is absorbing, so a small spontaneous infection probability $\alpha > 0$ is added to make the chain ergodic; let $\mu_n^{(\alpha)}$ be its unique stationary distribution and $\theta_1(\mathbf{x})$ the infected fraction.

**Binary models.** For a two-state model the limit drift of $\theta_1$ is a quadratic $p(z) = a_0 + a_1 z + a_2 z^2$ with $p(0) \ge 0 \ge p(1)$. If $p$ has a unique zero $z^*$ in $[0,1]$, every sequence of stationary distributions satisfies $\mu_n\{|\theta_1 - z^*| < \delta\} \to 1$ for every $\delta > 0$.

**SIS.** With contagion probability $b = \rho\,\phi_{01}(1) > 0$, recovery probability $c > 0$ and spontaneous infection probability $\alpha > 0$, $p(z) = \alpha + (b - c - \alpha)z - bz^2$, whose zero $z^*(\alpha)$ in $[0,1]$ satisfies $z^*(\alpha) \to z^* = \max\{1 - c/b, 0\}$. Hence

$$\lim_{\alpha\to 0^+}\lim_{n\to\infty}\mu_n^{(\alpha)}\{\mathbf{x} : |\theta_1(\mathbf{x}) - z^*| < \delta\} = 1\qquad\text{for every } \delta > 0:$$

the epidemic dies out when $c > b$ and settles at the endemic level $1 - c/b$ when $c < b$, on any ATM network and not only on the complete graph.

**SIRS.** With states susceptible, infected, recovered, contagion $b$, recovery $c$, loss of immunity $d$, spontaneous infection $\alpha > 0$, and $b > c > 0$, $d > 0$, the endemic point is

$$z_1^* = \frac{d(b-c)}{b(d+c)},\qquad z_2^* = \frac{c(b-c)}{b(d+c)}.$$

The functions $V_\alpha(\theta) = \theta_1 - (z_1^* + \alpha/b)\ln(\theta_1 + \alpha/b) + \frac{b}{2c}(\theta_2 - z_2^*)^2$ satisfy

$$\nabla V_\alpha\cdot\bar{D}_\alpha \le -b(\theta_1 - z_1^*)^2 - \frac{bd}{c}(\theta_2 - z_2^*)^2 + \frac{\alpha c}{b},$$

so the stationary distributions concentrate, in the limit $n \to \infty$ followed by $\alpha \to 0$, on the endemic proportions $(z_1^*, z_2^*)$.

## Depends on

- [Lyapunov concentration of stationary distributions of pairwise interaction network models](lyapunov-concentration-of-stationary-distributions-on-totally-mixing-networks.md)

## Expansion

For a binary model take $V(\theta) = (\theta_1 - z^*)^2$; since $p$ is positive below $z^*$ and negative above it, $\nabla V\cdot\bar{D} = 2(\theta_1 - z^*)p(\theta_1) \le 0$ with equality only at $z^*$, and the concentration theorem applies. For SIRS the Volterra-type logarithmic Lyapunov function is singular at $\theta_1 = 0$, so the shift by $\alpha/b$ makes it $C^2$ at the price of the error $\alpha c/b$, which the approximate-Lyapunov version absorbs. The order of limits matters: for fixed $\alpha = 0$ the finite chains are eventually absorbed in the disease-free state, but that happens on time scales that grow with $n$, and the stationary distribution of the slightly perturbed chain describes the long-lived endemic regime.

## Sources

- Giacomo Como, Fabio Fagnani and Sandro Zampieri, "An Invariance Principle-Based Concentration Result for Large-Scale Stochastic Pairwise Interaction Network Systems", IEEE Transactions on Automatic Control 71 (2026), 5064–5079, <https://doi.org/10.1109/tac.2026.3670758>; numbering as in arXiv:2410.22820: Proposition 3, Examples 5 and 7, Theorems 1 and 2.
