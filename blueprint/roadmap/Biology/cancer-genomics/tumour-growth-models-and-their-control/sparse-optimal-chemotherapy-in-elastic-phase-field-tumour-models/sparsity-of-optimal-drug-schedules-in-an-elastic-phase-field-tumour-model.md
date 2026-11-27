# Sparsity of optimal drug schedules in an elastic phase-field tumour model

**State system.** On a bounded domain $\Omega \subset \mathbb R^d$ ($d = 2,3$) with boundary split into a clamped part $\Gamma_D$ and a traction part $\Gamma_N$, let $\varphi$ be a phase field ($\varphi = 1$ tumour, $\varphi = -1$ healthy tissue), $\mu$ the chemical potential, $\sigma$ the nutrient and $\mathbf u$ the displacement with strain $\mathcal E(\mathbf u) = \tfrac12(\nabla\mathbf u + \nabla\mathbf u^\top)$. In $Q = \Omega\times(0,T)$:

$$\varphi_t = \Delta\mu + U(\varphi,\sigma,\mathcal E(\mathbf u)), \qquad \mu = -\Delta\varphi + \Psi'(\varphi) - \chi\sigma - \mathcal C(\mathcal E(\mathbf u) - \bar{\mathcal E} - \varphi\mathcal E^*) : \mathcal E^*,$$

$$\beta\sigma_t = \Delta\sigma + S(\varphi,\sigma), \qquad \mathbf 0 = \operatorname{div}\big(\mathcal C(\mathcal E(\mathbf u) - \bar{\mathcal E} - \varphi\mathcal E^*)\big),$$

with $\beta \ge 0$, a symmetric positive definite elasticity tensor $\mathcal C$ and Vegard's law for the eigenstrain. Boundary conditions are no-flux for $\varphi,\mu$, the Robin condition $\partial_n\sigma + \kappa(\sigma - w_1) = 0$, $\mathbf u = \mathbf 0$ on $\Gamma_D$ and a prescribed traction on $\Gamma_N$. Growth and nutrient terms are

$$U = \lambda_p\,\sigma f(\varphi)\, g\big(\mathcal C(\mathcal E(\mathbf u) - \bar{\mathcal E} - \varphi\mathcal E^*)\big) - (\lambda_a + w_2(t))\,k(\varphi), \qquad S = -h(\varphi)\big(\lambda_c\sigma - w_3(t)\big) + B(\sigma_c - \sigma),$$

with bounded Lipschitz $f,g,h,k$: $w_2(t)$ is a cytotoxic drug raising apoptosis, $w_3(t)$ a nutrient-modulating drug, and $w_1$ the boundary nutrient supply.

**Control problem.** Minimize

$$J = \frac{\alpha_\Omega}{2}\|\varphi(T) - \varphi_\Omega\|^2_{L^2(\Omega)} + \frac{\alpha_Q}{2}\|\varphi - \varphi_Q\|^2_{L^2(Q)} + \frac{\alpha_{\mathcal E}}{2}\int_Q n(x,\varphi)\,|\mathcal C(\mathcal E(\mathbf u) - \bar{\mathcal E} - \varphi\mathcal E^*)|^2 + \sum_{i=1}^3 \frac{\gamma_i}{2}\|w_i\|_{L^2}^2 + \gamma_4\|w_2\|_{L^1(0,T)} + \gamma_5\|w_3\|_{L^1(0,T)}$$

over box-constrained controls, with the drug controls non-negative: $0 \le w_i(t) \le \overline w$ for $i = 2,3$.

**Theorem.** Under the standing assumptions an optimal control exists, the control-to-state map is Fréchet differentiable, and first-order conditions hold with adjoint variables $(p,q,r,\mathbf s)$. For an optimal $\mathbf w^* = (w_1^*, w_2^*, w_3^*)$ with state $\varphi$:

- if $\gamma_2, \gamma_4 > 0$, then for a.e. $t$,

$$w_2^*(t) = 0 \iff \int_\Omega k(\varphi(x,t))\,p(x,t)\,dx \le \gamma_4;$$

- if $\gamma_3, \gamma_5 > 0$, then for a.e. $t$,

$$w_3^*(t) = 0 \iff \int_\Omega h(\varphi(x,t))\,r(x,t)\,dx \ge -\gamma_5.$$

**Corollary.** If $\gamma_2 > 0$, there is $\gamma_* > 0$ such that for $\gamma_4 > \gamma_*$ the zero schedule $w_2^* \equiv 0$ is optimal; similarly for $w_3$ when $\gamma_3 > 0$, $\beta > 0$ and $\gamma_5$ is large.

## Expansion

The variational inequality for $w_2^*$ reads $\int_0^T(\gamma_2 w_2^* + \gamma_4\lambda_2 - \int_\Omega k(\varphi)p)(y - w_2^*)\,dt \ge 0$ for all admissible $y$, with $\lambda_2 \in \partial|\cdot|(w_2^*)$. Since $w_2^* \ge 0$, it is the pointwise projection of $\gamma_2^{-1}(\int_\Omega k(\varphi)p - \gamma_4)$ onto $[0,\overline w]$, which vanishes exactly when the sensitivity $\int_\Omega k(\varphi)p$ does not exceed $\gamma_4$; the $L^1$ weight acts as a dose threshold. The corollary follows because the adjoint states are bounded in $L^\infty(0,T;L^2)$ uniformly over admissible controls, so a large enough $\gamma_4$ dominates the sensitivity for all $t$.

## Sources

- Harald Garcke, Kei Fong Lam, Andrea Signori, "Sparse Optimal Control of a Phase Field Tumor Model with Mechanical Effects", SIAM Journal on Control and Optimization 59 (2021), 1555–1580, <https://doi.org/10.1137/20m1372093>. Published version of arXiv:2010.03767, cited next; locators there refer to the arXiv version.
- Harald Garcke, Kei Fong Lam, Andrea Signori, "Sparse optimal control of a phase field tumour model with mechanical effects", arXiv (2020). Theorems 1–3, Theorem 5, Theorem 7, Corollary 5.1. <https://doi.org/10.48550/arXiv.2010.03767>
