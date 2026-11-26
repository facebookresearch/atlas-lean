# Wright–Fisher limit and absence of cutoff in the noisy voter model

**Model.** On the complete graph $\{1, \dots, n\}$, each site carries type $\eta_x \in \{0, 1\}$. With $X(\eta) = \sum_x \eta_x$ and fixed $a, b > 0$, site $x$ flips at rate $c_x(\eta)/n$, where
$$c_x(\eta) = (1 - \eta_x)\bigl(a + X(\eta)\bigr) + \eta_x\bigl(b + n - X(\eta)\bigr).$$
This is the noisy voter model: voter (Moran-type) copying plus spontaneous switching ("mutation") at rates $a/n$ and $b/n$. Its reversible invariant law $\mu_n^{a,b}$ makes the density $M = X/n$ asymptotically $\mathrm{Beta}(a, b)$. Let $x_t(m)$ solve the Wright–Fisher diffusion with mutation
$$dx_t = \bigl(a(1 - x_t) - b x_t\bigr)\,dt + \sqrt{2x_t(1 - x_t)}\,dB_t, \qquad x_0 = m.$$

**Theorem.**
1. *(Quantitative diffusion limit.)* There is $C = C(a, b) < \infty$ such that for every $n$, every $t \ge 0$ and every initial configuration,
$$d_K\bigl(M_{nt}, x_t(M_0)\bigr) \le \frac{C \min\{1, t^{1/4}\}}{\sqrt n},$$
where $d_K$ is the Kantorovich (Wasserstein-1) distance.
2. *(Thermalization of positions.)* Fix $\alpha < 1/3$ and restrict to configurations $\sigma$ with $M(\sigma)(1 - M(\sigma)) \ge n^{-\alpha}$. With $t_n = \tfrac12\log n + \log\bigl(M(\sigma)(1 - M(\sigma))\bigr) + \tau$, the law at time $t_n$ started from $\sigma$ and the law started from a uniformly random rearrangement $u(\sigma)$ of $\sigma$ satisfy, uniformly in such $\sigma$,
$$\frac{1}{\sqrt n}\, d_K\bigl(\sigma P_{t_n}, u(\sigma) P_{t_n}\bigr) \to 2e^{-\tau}$$
in the normalized Hamming metric.
3. *(No cutoff.)* If $X(\sigma^n)/n \to m_0 \in (0, 1)$, the mixing time $t^n_{\mathrm{mix}}(\varepsilon)$ in normalized Kantorovich distance satisfies $t^n_{\mathrm{mix}}(\varepsilon)/n \to \mathcal G^{-1}(\varepsilon; m_0)$, where $\mathcal G(t; m) = d_K(x_t(m), \mathrm{Beta}(a, b))$ is continuous and strictly decreasing. The convergence profile is the Wright–Fisher relaxation curve, not a step, so there is no cutoff.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../../coalescent-theory/structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

The particle count is itself a birth–death chain whose generator, on time scale $n$, converges to the Wright–Fisher generator with mutation; a Stein-type quantitative CLT with regularity of the Fokker–Planck equation gives the $n^{-1/2}$ rate. Within time $O(\log n)$ the model keeps its particle count but forgets *where* the particles are: local densities relax exponentially at rate $1$ around the global density, with fluctuations of order $n^{-1/2}$, which produces the $2e^{-\tau}$ profile at time $\tfrac12\log n$. Forgetting the count takes time of order $n$ and follows the diffusion, whose distance to its Beta stationary law decays smoothly, hence no cutoff.

## Sources

- E. Aljovin, M. Jara and Y. Xiang, "Thermalization And Convergence To Equilibrium Of The Noisy Voter Model", arXiv:2409.05722 (2024), Theorem 3.1, Theorem 4.1 and Section 2.3, <https://doi.org/10.48550/arXiv.2409.05722>.
