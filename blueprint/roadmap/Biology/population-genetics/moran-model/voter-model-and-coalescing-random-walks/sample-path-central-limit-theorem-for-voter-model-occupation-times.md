# Sample path central limit theorem for voter model occupation times

**Setting.** Let $(\eta_t)$ be the voter model on $\mathbb Z^d$, $d \ge 3$, started from its invariant law $\nu_p$, $p \in (0, 1)$ (the limit from Bernoulli($p$) product measure). The occupation time of the origin is $\int_0^t \eta_s(O)\,ds$, with mean $pt$. Let $\gamma_d$ be the probability that continuous-time simple random walk started at a neighbour of $O$ never visits $O$, $p_{s,d}(O, O)$ its return kernel, and

$$h_d(t) = \begin{cases} t^{3/4}, & d = 3,\\ \sqrt{t\log t}, & d = 4,\\ \sqrt t, & d \ge 5,\end{cases} \qquad C_d = \begin{cases} \sqrt{4p(1-p)\gamma_3/\pi^{3/2}}, & d = 3,\\ \sqrt{\gamma_4 p(1-p)/\pi^2}, & d = 4,\\ \sqrt{4dp(1-p)\gamma_d\int_0^\infty s\,p_{s,d}(O,O)\,ds}, & d \ge 5.\end{cases}$$

**Theorem.** For every $T > 0$, as $N \to \infty$,

$$\left\{\frac{1}{h_d(N)}\int_0^{tN}\bigl(\eta_s(O) - p\bigr)\,ds\right\}_{0 \le t \le T} \Longrightarrow \{\Lambda_t\}_{0 \le t \le T}$$

in $C[0, T]$, where $\Lambda = C_d W$ with $W$ a standard Brownian motion when $d \ge 4$, and $\Lambda = C_3\zeta$ when $d = 3$, $\zeta$ being the centred continuous Gaussian process with

$$\mathrm{Cov}(\zeta_t, \zeta_s) = s^{3/2} + t^{3/2} - \tfrac12(t - s)^{3/2} - \tfrac12(t + s)^{3/2}, \qquad 0 \le s \le t,$$

a sub-fractional Brownian motion with Hurst index $3/4$. This upgrades the one-dimensional-marginal CLT of Cox and Griffeath to a functional limit.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../../../coalescent-theory/structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

Duality with coalescing random walks turns covariances $\mathrm{Cov}(\eta_s(O), \eta_u(O))$ into probabilities that two lineages started at $O$ at times $s$ and $u$ coalesce, which decay like $|u - s|^{1 - d/2}$. Integrating gives variance of order $t^{3/2}$ in $d = 3$, $t\log t$ in $d = 4$ and $t$ in $d \ge 5$, which sets $h_d$. In $d \ge 4$ correlations are summable on the scale $h_d$ and a resolvent (Kipnis–Varadhan) martingale decomposition yields a Brownian limit. In $d = 3$ long-range correlations persist; finite-dimensional convergence to $\zeta$ comes from a Poisson flow representation, and tightness from moment bounds.

## Sources

- Xiaofeng Xue, "Sample path central limit theorem for the occupation time of the voter model on a lattice", Stoch. Process. Appl. 196 (2026), 104920, <https://doi.org/10.1016/j.spa.2026.104920>. Numbering follows the arXiv version, arXiv:2412.05064 (2024): Proposition 1.1 and Theorem 2.1, <https://doi.org/10.48550/arXiv.2412.05064>.
