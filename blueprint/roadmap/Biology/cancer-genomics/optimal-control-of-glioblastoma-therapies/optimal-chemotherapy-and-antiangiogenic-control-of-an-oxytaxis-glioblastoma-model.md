# Optimal chemotherapy and antiangiogenic control of an oxytaxis glioblastoma model

**Setting.** On a bounded smooth planar domain $\Omega$ over $Q = \Omega\times(0,T)$, glioblastoma cell density $u$ and oxygen concentration $\sigma$ follow a Keller–Segel type system with homogeneous Neumann conditions:

$$\partial_t u = D_u\Delta u + \rho(\sigma)\,u(\alpha - u) - \kappa\,\mathsf{c}\,u\,\sigma - \chi\,\nabla\cdot(u\nabla\sigma),$$

$$\partial_t\sigma = D_\sigma\Delta\sigma + P_{er}S_v(\beta - \sigma) - \frac{A_{ox}\,u\,\sigma}{k_{ox} + \sigma} + (1 - \mathsf{s})\,S_c\,u,$$

where oxytaxis ($\chi \ge 0$) drives cells up oxygen gradients, $\rho(\sigma) = \frac{\hat\rho}{\alpha}\big(\frac{\sigma}{\beta} + b(1 - \frac{\sigma}{\beta})\big)$ lowers proliferation under hypoxia, the last oxygen term is angiogenic supply produced by tumour cells, and the controls are a cytotoxic drug $\mathsf{c}(x,t) \in [0,1]$, whose effect $\kappa\mathsf{c}u\sigma$ depends on oxygen, and an antiangiogenic drug $\mathsf{s}(x,t) \in [0,1]$. Admissible controls also satisfy a total chemotherapy budget $\int_Q \mathsf{c} \le c_{\max} < T|\Omega|$. The cost, with bounded positive weights, is

$$J = \int_Q\Big[\frac{k_1}{2}u^2 + \frac{k_2}{2}(\sigma - \sigma_Q)^2 + k_3\,\mathsf{c} + k_4\,\mathsf{s}\Big] + \int_\Omega\Big\frac{l_1}{2}u^2 + \frac{l_2}{2}(\sigma - \sigma_\Omega)^2\Big.$$

**Theorem.**
1. (Well-posedness.) For $u_0 \in L^2(\Omega)$, $\sigma_0 \in H^1(\Omega)$ nonnegative and bounded controls with $0 \le \mathsf{s} \le 1$, there is a unique nonnegative weak–strong solution, $u \in C(L^2) \cap L^2(H^1)$ with $\partial_t u \in L^2(H^{-1})$ and $\sigma$ in the maximal-regularity space $X_2$; solutions depend Lipschitz-continuously on initial data and controls.
2. (Existence.) The control problem has at least one global optimal solution.
3. (First-order conditions.) For a local optimal control $(\mathsf{c}^\ast,\mathsf{s}^\ast)$ there is a unique adjoint pair $(p_1,p_2)$ solving the backward linearised system, with terminal data $p_1(T) = l_1u^\ast(T)$, $p_2(T) = l_2(\sigma^\ast(T) - \sigma_\Omega)$ (in a weaker space when $l_1 \ne 0$), and for all admissible $(\bar{\mathsf{c}},\bar{\mathsf{s}})$

$$\int_Q\Big[(k_3 - u^\ast\sigma^\ast p_1)(\bar{\mathsf{c}} - \mathsf{c}^\ast) + (k_4 - u^\ast p_2)(\bar{\mathsf{s}} - \mathsf{s}^\ast)\Big] \ge 0 .$$

## Expansion

The oxytaxis term $\nabla\cdot(u\nabla\sigma)$ couples the equations through the oxygen gradient, so the analysis pairs an energy-level (weak) solution for the cells with a strong solution for oxygen, whose second derivatives are needed to control the cross term; this is the weak–strong framework. Existence of an optimal control follows from the uniform estimates and weak-star compactness of the convex, budget-constrained control set. The variational inequality says that chemotherapy pays where its marginal benefit $u^\ast\sigma^\ast p_1$ exceeds its unit cost $k_3$, so cytotoxic treatment concentrates where tumour cells meet oxygen, and antiangiogenic treatment where $u^\ast p_2$ exceeds $k_4$. Since the admissible set is convex, the optimal controls are projections of these switching quantities onto the admissible set, and for the budget-constrained chemotherapy the projection onto $\{0 \le \mathsf{c} \le 1,\ \int_Q \mathsf{c}\,\rho \le c_{\max}\}$ has a known explicit characterisation that is used in the numerical scheme.

## Sources

- Juan J. Forero-Hernández, Francisco Guillén-González, Élder J. Villamizar-Roa, "Optimal control of therapies related to an oxytaxis glioblastoma model", arXiv:2604.21674 (2026), Section 1 (model, cost functional, Definition 1.1, Theorems 1.2–1.4), Section 2 (Theorem 2.1), Section 3 (Proposition 3.1, Theorem 3.2, variational inequality, Remark 3.3, Proposition 3.4) and Appendices, <https://doi.org/10.48550/arXiv.2604.21674>.
