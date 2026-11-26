# Optimal age- and location-targeted vaccination in a structured epidemic model

Take the nonlocal age- and space-structured epidemic model of [the well-posedness page](well-posedness-of-nonlocal-age-and-space-structured-epidemic-models.md), with vaccination entering through a control term $K(u)\, y$ that is linear in $u$. Vaccination is delivered at $M$ disjoint centers $\Omega_1, \dots, \Omega_M \subset \Omega$ and to $N$ age classes $[a_{j-1}, a_j]$:

$$ u(t,a,x) = \sum_{i=1}^{M} \sum_{j=1}^{N} u_{ij}(t)\, \mathbf 1_{\Omega_i}(x)\, \mathbf 1_{[a_{j-1}, a_j]}(a), \qquad 0 \le u_{ij}(t) \le \bar u . $$

With a weight vector $g$ (for instance selecting the infectives) and a cost weight $\alpha \ge 0$, minimize

$$ J(u,y) = \frac12 \int_0^T \int_0^{a_{\max}} \int_\Omega |g \cdot y(t,a,x)|^2\, dx\, da\, dt + \frac{\alpha}{2} \int_0^T \|u(t)\|^2_{\mathbb R^{M\times N}}\, dt $$

over admissible controls and the corresponding states.

**Existence.** Suppose either (C1) the cost is augmented by $\frac{\alpha_d}{2} \|\partial_t u\|^2_{L^2}$ with $\alpha_d > 0$, or (C2) the controls also satisfy $\|\partial_t u\|_{L^p((0,T))} \le \bar u_d$ for some $1 < p \le \infty$. Then the optimal control problem has a solution.

**First-order conditions.** The adjoint equation

$$ -(\partial_t + \partial_a) p + (L + \Lambda(y) + \tilde K(u))^{\top} p + \tilde\Lambda_{y}(p) - \sigma\Delta p - \beta(a,x)^{\top} p(t, 0, x) = -g^{\top} g\, y, \qquad p(T,\cdot,\cdot) = 0, \quad p(t, a_{\max}, \cdot) = 0, $$

with Neumann conditions, has a unique solution; here $\tilde\Lambda_y$ is the linear nonlocal operator coming from differentiating $\Lambda(y) y$ in $y$. Every optimal pair $(y^*, u^*)$ with adjoint $p^*$ satisfies the variational inequality

$$ \left(\alpha u^* + \tilde K^{*}\big(\operatorname{diag}(y^* \odot p^*)\big),\; u - u^*\right)_{L^2((0,T), \mathbb R^{M\times N})} \ge 0 \quad \text{for all admissible } u . $$

The term $\beta^{\top} p(t,0,x)$ is produced by the renewal condition at age zero: newborn susceptibles carry the shadow value of the age-zero boundary back to every reproductive age.

## Depends on

- [Well-posedness of nonlocal age- and space-structured epidemic models](well-posedness-of-nonlocal-age-and-space-structured-epidemic-models.md)

## Expansion

The difficulty in the existence proof is compactness: the state is controlled only in $y$, $\nabla_x y$ and $(\partial_t + \partial_a) y$, not in $\partial_t y$ and $\partial_a y$ separately, so Aubin–Lions does not apply to the state. The extra time regularity of the control (C1 or C2) makes a minimizing sequence bounded in $W^{1,p}((0,T))$, hence strongly convergent in $C([0,T])$, so the bilinear vaccination term passes to the limit and the direct method closes. For the optimality system, the linearized state operator is shown to be boundedly invertible by the same cohort-wise construction used for the state, the adjoint equation is reversed in time and age to the same form, and the variational inequality follows from the standard Lagrangian argument for control-constrained problems. In numerical experiments on an SVIR model, the optimal policy vaccinates early in the epidemic and prioritizes younger age classes later. These are Theorems 3.1 and 4.4 and Corollary 4.5 of the source.

## Sources

- B. Azmi and N. Schlosser, *Optimal Control of General Nonlocal Epidemic Models with Age and Space Structure*, arXiv:2503.01466 (2025), Theorem 3.1, Theorem 4.4, Corollary 4.5. <https://doi.org/10.48550/arXiv.2503.01466> Published version: Journal of Differential Equations 464 (2026) 114250, <https://doi.org/10.1016/j.jde.2026.114250>.
