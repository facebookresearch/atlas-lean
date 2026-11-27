# Well-posedness and optimal mobility control of a SEIR model with heterogeneous diffusion

**Model.** On a bounded smooth connected domain $\Omega \subset \mathbb R^d$ ($d \le 3$), $Q = \Omega\times(0,T)$, let $s,e,i,r$ be susceptible, exposed, infectious and recovered densities, $n = s + e + i + r$, and

$$\partial_t s + \beta_i s\,i + \beta_e s\,e - \operatorname{div}(\kappa_s\nabla s) - \gamma r = 0,$$

$$\partial_t e - \beta_i s\,i - \beta_e s\,e + \sigma e + \phi_e e - \operatorname{div}(\kappa_e\nabla e) = 0,$$

$$\partial_t i + \phi_r i - \operatorname{div}(\kappa_i\nabla i) - \sigma e = 0, \qquad \partial_t r - \phi_r i - \phi_e e - \operatorname{div}(\kappa_r\nabla r) + \gamma r = 0,$$

with homogeneous Neumann conditions and nonnegative initial data. Here $\sigma$ is the incubation rate, $\phi_e, \phi_r$ recovery rates of exposed and infectious individuals, $\gamma(t) \in [0,\gamma_{\max}]$ the loss of immunity, and the transmission rates $\beta_i, \beta_e \in [0,\beta_{\max}]$ and diffusion coefficients $\kappa_s,\kappa_e,\kappa_i,\kappa_r \in [\kappa_{\min},\kappa_{\max}]$ ($\kappa_{\min} > 0$) are Carathéodory functions of $(x,t)$ and the total density $n$.

**Theorem (existence).** There is a weak solution $(s,e,i,r)$ in $H^1(0,T;V') \cap C^0([0,T];H) \cap L^2(0,T;V) \cap L^\infty(Q)$ ($H = L^2(\Omega)$, $V = H^1(\Omega)$), nonnegative, with a norm bound depending only on $\Omega$, $T$, $\kappa_{\min},\kappa_{\max},\beta_{\max},\gamma_{\max},\phi_e,\phi_r,\sigma$ and the initial data.

**Theorem (uniqueness).** If all four diffusion coefficients coincide and depend only on $n$, the solution is unique. If instead the diffusion coefficients do not depend on $n$ (they may differ and depend on $(x,t)$) and $\beta_i,\beta_e$ are Lipschitz in $n$, the solution is unique and depends continuously on the diffusion coefficients.

**Theorem (optimal mobility control).** Let $\Omega$ be the disjoint union of measurable subdomains $\Omega_1,\dots,\Omega_m$ with $|\Omega_j| > 0$, and $Q_j = \Omega_j\times(0,T)$. Treat $(\kappa_s,\kappa_e,\kappa_i,\kappa_r)$, independent of $n$, as controls that are constant on each $Q_j$: $\mathcal U_{ad} = \mathcal U^s_{ad}\times\mathcal U^e_{ad}\times\mathcal U^i_{ad}\times\mathcal U^r_{ad}$ with $\mathcal U^s_{ad} = \{\kappa_s = \sum_{j=1}^m u^s_j\chi_{Q_j} : u^s_j \in [u^{s,j}_{\min},u^{s,j}_{\max}]\}$ and likewise for $e,i,r$, for fixed closed intervals inside $[\kappa_{\min},\kappa_{\max}]$ (the source's (1.9), (1.12)–(1.13)). This $\mathcal U_{ad}$ is closed, convex, and spans a finite-dimensional subspace of $L^\infty(Q)^4$ (the source's (2.31)–(2.33)), which the existence proof needs: weak-star limits of general diffusion coefficients do not pass to the state. For a measurable target region $\Omega_C \subset \Omega$, $Q_C = \Omega_C\times(0,T)$ and $\alpha > 0$, minimize

$$\mathcal J = \frac12\int_{Q_C}\big(|e|^2 + |i|^2\big) + \frac\alpha2\int_Q\big(|\kappa_s|^2 + |\kappa_e|^2 + |\kappa_i|^2 + |\kappa_r|^2\big).$$

An optimal control exists, and first-order necessary conditions hold in terms of an adjoint system.

## Expansion

Summing the four equations shows that $n$ solves a scalar parabolic equation in divergence form when the diffusion coefficients coincide, and the reaction terms cancel; this gives $L^\infty$ control of $n$ and, with nonnegativity from truncation, $L^\infty$ bounds on each component, hence the stability estimate via Faedo–Galerkin approximation and compactness. Uniqueness in the equal-coefficient case uses that $n$ is determined by a scalar equation (written through a Kirchhoff-type transform $\Phi$), after which the remaining system is semilinear with known coefficients. With $n$-independent coefficients, contraction estimates in $L^2$ give continuous dependence, which yields weak-star lower semicontinuity of $\mathcal J$ along minimizing sequences of controls and hence existence of an optimal control.

## Sources

- Pierluigi Colli, Gianni Gilardi, Gabriela Marinoschi, "Global Solution and Optimal Control of an Epidemic Propagation with a Heterogeneous Diffusion", Applied Mathematics & Optimization 89 (2024), 28, <https://doi.org/10.1007/s00245-023-10094-2>. Published version of arXiv:2308.08251, cited next; locators there refer to the arXiv version.
- Pierluigi Colli, Gianni Gilardi, Gabriela Marinoschi, "Global solution and optimal control of an epidemic propagation with a heterogeneous diffusion", arXiv (2023). Section 2 (assumptions; existence, uniqueness and continuous-dependence theorems), Section 4 (control problem, existence of an optimal control, necessary conditions). <https://doi.org/10.48550/arXiv.2308.08251>
