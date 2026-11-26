# Backward uniqueness and stability for a Cahn–Hilliard tumour model

**Model.** In a bounded domain $\Omega$ over $(0,T)$, the tumour volume fraction $\phi$ ($\phi \equiv 0$ healthy, $\phi \equiv 1$ tumour), its chemical potential $\mu$ and a nutrient concentration $\sigma$ solve the phase-field tumour growth system

$$\partial_t\phi - \Delta\mu = P(\phi)\big(\sigma + \chi(1-\phi) - \mu\big) - c(x,t)\,h(\phi), \qquad \mu = -\Delta\phi + F'(\phi) - \chi\sigma,$$

$$\partial_t\sigma - \Delta\sigma + \chi\Delta\phi = -P(\phi)\big(\sigma + \chi(1-\phi) - \mu\big) + \kappa(1-\sigma),$$

with homogeneous Neumann conditions, a proliferation function $P$, a double-well potential $F$, a chemotaxis coefficient $\chi$, a treatment term $c\,h(\phi)$, and initial data $(\phi_0,\sigma_0)$ in an admissible set $\mathcal I_{\rm ad}$ of $H^2\times H^1$ data bounded by a constant $M$. Under the paper's structural assumptions there is a unique strong solution.

**Inverse problem.** Recover past states, in particular the initial tumour configuration, from a single observation $(\phi(T),\sigma(T))$ at the final time.

**Theorem (Hölder stability at positive times).** For two strong solutions with data in $\mathcal I_{\rm ad}$ and $\lambda>0$ large, there is $C_1 = C_1(\lambda,T,\text{parameters})$ such that for every $t_0 \in (0,T)$

$$\|(\phi_1,\sigma_1)(t_0) - (\phi_2,\sigma_2)(t_0)\|_{L^2\times L^2} \le C_1M^{1-\theta(t_0)}\,\|(\phi_1,\sigma_1)(T) - (\phi_2,\sigma_2)(T)\|_{H^2\times H^1}^{\theta(t_0)}, \qquad \theta(t_0) = \frac{e^{\lambda t_0}-1}{3e^{\lambda T} - 2e^{\lambda t_0} - 1} \in (0,1),$$

whenever the final-time discrepancy is small enough.

**Corollary (backward uniqueness).** If two solutions coincide at time $T$, they coincide on $[0,T]$; in particular their initial data are equal. No smallness of the chemotaxis coefficient $\chi$ is needed, unlike earlier logarithmic-convexity arguments.

**Theorem (logarithmic stability of the initial datum).**

$$\|(\phi_{0,1},\sigma_{0,1}) - (\phi_{0,2},\sigma_{0,2})\|_{L^2\times L^2} \le C_2\Big(\log\frac{M}{\|(\phi_1,\sigma_1)(T) - (\phi_2,\sigma_2)(T)\|_{H^2\times H^1}}\Big)^{-1/4},$$

with $C_2 = 2M_1^{3/4}C_1^{1/4}/\beta^{1/4}$, $\beta = \lambda/(3e^{\lambda T} - 3)$. On finite-dimensional admissible sets this improves to Lipschitz stability, which supports convergence of discretized reconstruction algorithms.

## Expansion

The key tool is a Carleman estimate for the coupled fourth-order (Cahn–Hilliard) / second-order (reaction–diffusion) parabolic system with cross-diffusion terms, using time-only weights $e^{\lambda t}$-type functions; such weights give Hölder interpolation between the a priori bound $M$ and the final-time discrepancy, with exponent $\theta(t_0)$ degenerating as $t_0 \to 0$. Letting $t_0 \to 0$ and optimizing over $t_0$ against the regularity bound $M_1$ yields the logarithmic rate for the initial datum, and the uniqueness statement is the special case of zero discrepancy.

## Sources

- Abramo Agosti, Elena Beretta, Cecilia Cavaterra and Matteo Fornoni, "Carleman estimates for backward Cahn-Hilliard-reaction-diffusion problems", arXiv:2606.16904 (2026), Theorem 2.1 (Carleman estimate), Theorems 3.1 and 3.2 (abstract stability), Theorem 4.1 (strong solutions), Theorem 4.4, Corollary 4.5, Theorem 4.7 and Theorem 4.13 (tumour model), <https://doi.org/10.48550/arXiv.2606.16904>.
