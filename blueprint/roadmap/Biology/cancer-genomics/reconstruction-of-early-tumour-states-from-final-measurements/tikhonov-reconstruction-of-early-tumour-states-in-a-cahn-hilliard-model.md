# Tikhonov reconstruction of early tumour states in a Cahn-Hilliard-reaction-diffusion model

**Model.** On a bounded smooth domain $\Omega\subset\mathbb{R}^N$ ($N\le3$), the tumour phase field $\phi$ ($\phi\approx1$ tumour, $\phi\approx0$ healthy tissue), chemical potential $\mu$ and nutrient $\sigma$ satisfy

$$\partial_t\phi-\Delta\mu=P(\phi)\bigl(\sigma+\chi(1-\phi)-\mu\bigr)-c(x,t)\,h(\phi),\qquad \mu=-\Delta\phi+F'(\phi)-\chi\sigma,$$

$$\partial_t\sigma-\Delta\sigma+\chi\Delta\phi=-P(\phi)\bigl(\sigma+\chi(1-\phi)-\mu\bigr)+(1-\sigma),$$

with homogeneous Neumann conditions for $\phi,\mu,\sigma$, a double-well potential $F$, proliferation function $P\ge0$, chemotaxis coefficient $\chi$, and a given cytotoxic treatment term $c\,h(\phi)$. Let $\mathcal{R}(\phi_0,\sigma_0)=(\phi(T),\sigma(T))$ be the map from initial to final state. The inverse problem is to recover $(\phi_0,\sigma_0)$ from a single measurement $(\phi_{\mathrm{meas}},\sigma_{\mathrm{meas}})$ at time $T$; backward parabolic problems are severely ill-posed.

**Theorem.**

1. (Backward uniqueness.) For sufficiently regular initial data and chemotaxis coefficient with $\chi^2<2$ (keeping the leading operator uniformly elliptic), if two strong solutions coincide at time $T$, then they coincide on all of $[0,T]$; in particular the initial data are equal. So $\mathcal{R}$ is injective on regular data.
2. (Existence of a regularized reconstruction.) The Tikhonov problem of minimizing

$$\mathcal{J}(\phi_0,\sigma_0)=\frac{\lambda_1}{2}\|\phi(T)-\phi_{\mathrm{meas}}\|^2_{L^2}+\alpha_1\int_\Omega\Bigl(F(\phi_0)+\tfrac12|\nabla\phi_0|^2\Bigr)dx+\frac{\lambda_2}{2}\|\sigma(T)-\sigma_{\mathrm{meas}}\|^2_{L^2}+\frac{\alpha_2}{2}\|\sigma_0\|^2_{L^2}$$

over $\phi_0\in H^1(\Omega)$, $\sigma_0\in L^2(\Omega)$ with $0\le\phi_0,\sigma_0\le1$ a.e. admits at least one minimizer. The Ginzburg-Landau term is the phase-field version of the interface perimeter, suited to initial states made of well-separated phases.

3. (Optimality.) $\mathcal{R}:H^1\times L^2\to L^2\times L^2$ is Fréchet differentiable, its derivative given by a linearized system; the adjoint system $(p,q,r)$ is uniquely solvable backward in time with final data driven by the misfits $\lambda_1(\phi(T)-\phi_{\mathrm{meas}})$ and $\lambda_2(\sigma(T)-\sigma_{\mathrm{meas}})$; and every minimizer satisfies the variational inequality

$$\int_\Omega p(0)(\phi_0-\bar\phi_0)+\alpha_1\bigl(F'(\bar\phi_0)(\phi_0-\bar\phi_0)+\nabla\bar\phi_0\cdot\nabla(\phi_0-\bar\phi_0)\bigr)dx+\int_\Omega\bigl(r(0)+\alpha_2\bar\sigma_0\bigr)(\sigma_0-\bar\sigma_0)\,dx\ \ge\ 0$$

for all admissible $(\phi_0,\sigma_0)$, which drives a projected-gradient reconstruction algorithm.

## Expansion

1. Backward uniqueness follows the log-convexity (Agmon-Nirenberg) method: for the difference of two solutions, the ratio of the Dirichlet-type energy to the $L^2$ norm satisfies a differential inequality, so a solution vanishing at $T$ vanishes identically; the condition $\chi^2<2$ controls the chemotactic cross terms.
2. Existence of a minimizer uses the coercivity of the Ginzburg-Landau and $L^2$ penalties, weak compactness of the admissible sets, and weak-to-strong continuity of $\mathcal{R}$ from continuous dependence estimates.
3. Differentiating $\mathcal{J}\circ\mathcal{R}$ and transposing the linearized system yields the adjoint equations and the variational inequality.

## Sources

- Abramo Agosti, Elena Beretta, Cecilia Cavaterra, Matteo Fornoni and Elisabetta Rocca, *Identifying early tumour states in a Cahn-Hilliard-reaction-diffusion model*, arXiv:2409.15925 (Theorems 3.2 and 3.3, Theorem 4.4, Corollary 4.7, Theorems 5.2, 5.5, 5.6 and 5.8). <https://doi.org/10.48550/arXiv.2409.15925> Published version: Mathematical Models and Methods in Applied Sciences 35 (2025) 2329–2394, <https://doi.org/10.1142/s0218202525500411>.
