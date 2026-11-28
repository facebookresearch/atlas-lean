# Optimal control of transmission rates in a reaction-diffusion SEIRS model

**Setting.** On a bounded smooth domain $\Omega \subset \mathbb{R}^d$, $d \le 3$, over $Q = \Omega \times (0,T)$, densities of susceptible $s$, exposed (infectious but asymptomatic) $e$, symptomatic infected $i$ and recovered $r$ individuals diffuse with bounded coefficients $\kappa_s, \kappa_e, \kappa_i, \kappa_r \in [\kappa_{\min}, \kappa_{\max}]$, under homogeneous Neumann conditions:

$$\partial_t s - \nabla\cdot(\kappa_s\nabla s) + (u_i\,s\,i + u_e\,s\,e) - \gamma r = 0, \qquad \partial_t e - \nabla\cdot(\kappa_e\nabla e) - (u_i\,s\,i + u_e\,s\,e) + (\sigma + \phi_e)\,e = 0,$$

$$\partial_t i - \nabla\cdot(\kappa_i\nabla i) + \phi_r\,i - \sigma e = 0, \qquad \partial_t r - \nabla\cdot(\kappa_r\nabla r) - (\phi_r i + \phi_e e) + \gamma r = 0,$$

with constants $\sigma, \phi_e, \phi_r > 0$, loss of immunity $\gamma(t) \ge 0$, nonnegative bounded initial data, and space-time dependent transmission rates $u_i, u_e \in L^\infty(Q)$, $0 \le u_i, u_e \le M$, acting as controls. The cost penalises the excess of the total infectious population over a threshold $\Lambda > 0$ at the final time and the control effort:

$$\mathcal{J}(u_i,u_e) = \frac12\int_\Omega \Big(\big((e+i)(T) - \Lambda\big)^+\Big)^2 + \frac12\int_Q \big(u_i^2 + u_e^2\big),$$

over admissible controls $0 \le u_i \le u_i^{\max}$, $0 \le u_e \le u_e^{\max}$.

**Theorem.**
1. (Well-posedness.) There is a unique variational solution $(s,e,i,r) \in H^1(0,T;V^\ast) \cap L^2(0,T;V) \cap L^\infty(Q)$, $V = H^1(\Omega)$, which is nonnegative, with a bound independent of the controls.
2. (Lipschitz dependence.) Solutions depend Lipschitz-continuously on the controls: the difference of two solutions in $C^0([0,T];L^2) \cap L^2(0,T;V)$ is bounded by a constant times the $L^2(Q)$ distance of the controls.
3. (Existence.) The control problem has an optimal control $(u_i^\ast,u_e^\ast)$.
4. (First-order conditions.) With adjoint variables $(p,q,w,z)$ solving the backward parabolic system

$$-\partial_t p - \nabla\cdot(\kappa_s\nabla p) + (u_i^\ast i^\ast + u_e^\ast e^\ast)(p - q) = 0, \qquad -\partial_t q - \nabla\cdot(\kappa_e\nabla q) + (\sigma + \phi_e)q + u_e^\ast s^\ast(p - q) - \sigma w - \phi_e z = 0,$$

$$-\partial_t w - \nabla\cdot(\kappa_i\nabla w) + \phi_r(w - z) + u_i^\ast s^\ast(p - q) = 0, \qquad -\partial_t z - \nabla\cdot(\kappa_r\nabla z) + \gamma(z - p) = 0,$$

with Neumann conditions, $p(T) = z(T) = 0$ and $q(T) = w(T) = \big((e^\ast + i^\ast)(T) - \Lambda\big)^+$, every admissible $(u_i,u_e)$ satisfies

$$\int_Q \big(s^\ast i^\ast(q - p) + u_i^\ast\big)(u_i - u_i^\ast) + \int_Q \big(s^\ast e^\ast(q - p) + u_e^\ast\big)(u_e - u_e^\ast) \ge 0 .$$

## Expansion

The a priori estimates give nonnegativity and an $L^\infty$ bound independent of the controls, which is what makes the bilinear incidence terms Lipschitz. Existence of an optimal control follows from weak-star compactness of the box of admissible controls together with these uniform estimates, which let the bilinear terms pass to the limit. The control-to-state map is Fréchet differentiable, and the adjoint system is its transpose; only the exposed and infected adjoints carry terminal data, because only $e + i$ enters the terminal cost. The variational inequality is the projection formula: pointwise, $u_i^\ast$ is the projection of $s^\ast i^\ast(p - q)$ onto $[0, u_i^{\max}]$, so transmission is reduced most where susceptibles meet infectives and the shadow value of a new infection, $q - p$, is largest.

## Sources

- Pierluigi Colli, Gianni Gilardi, Gabriela Marinoschi, Elisabetta Rocca, "Optimal control of a reaction–diffusion model related to the spread of COVID-19", Analysis and Applications 22 (2024), 111–136, <https://doi.org/10.1142/s0219530523500197>. Published version of arXiv:2304.11114, cited next; locators there refer to the arXiv version.
- Pierluigi Colli, Gianni Gilardi, Gabriela Marinoschi, Elisabetta Rocca, "Optimal control of a reaction-diffusion model related to the spread of COVID-19", arXiv:2304.11114 (2023), Section 2 (assumptions, well-posedness and continuous-dependence theorems, control problem, optimality condition and adjoint system), Sections 3–4 (proofs), <https://doi.org/10.48550/arXiv.2304.11114>.
