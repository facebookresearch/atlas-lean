# Pontryagin optimality system with quadratic control costs

**Setting.** Let $x(t) \in \mathbb{R}^n_{\ge 0}$ be the state of a compartmental epidemic model on a finite horizon $[0, T]$,

$$\dot x = f(x, u), \qquad x(0) = x_0,$$

with $f$ continuously differentiable and affine in the control vector $u = (u_1, \dots, u_k)$, each control Lebesgue measurable with $u_i(t) \in [0, u_i^{\max}]$ (the admissible set $\mathcal{U}$). Minimize

$$J(u) = \int_0^T \Big( \sum_{j} A_j x_j(t) + \sum_{i=1}^{k} B_i u_i(t)^2 \Big)\, dt,$$

where $A_j \ge 0$ weight the infected compartments and $B_i > 0$ are relative control costs.

**Existence.** If solutions of the state system are bounded on $[0,T]$ uniformly in $u \in \mathcal{U}$, the right-hand side is bounded by a linear function of the state and control, $\mathcal{U}$ is closed and convex, and the integrand is convex in $u$ (here, quadratic with $B_i > 0$), then an optimal control $u^* \in \mathcal{U}$ exists (Fleming–Rishel existence theorem).

**Necessary conditions.** With Hamiltonian

$$H(x, u, \lambda) = \sum_j A_j x_j + \sum_i B_i u_i^2 + \sum_{m=1}^{n} \lambda_m f_m(x, u),$$

for an optimal pair $(x^*, u^*)$ there exist adjoint variables $\lambda(t)$ satisfying

$$\dot\lambda_m = -\frac{\partial H}{\partial x_m}(x^*, u^*, \lambda), \qquad \lambda_m(T) = 0 \ (\text{transversality}),$$

and $u^*(t)$ minimizes $H(x^*(t), \cdot, \lambda(t))$ over the box $\prod_i [0, u_i^{\max}]$. Because $H$ is strictly convex and quadratic in each $u_i$, the minimizer is the projection of the stationary point:

$$u_i^*(t) = \min\Big\{ u_i^{\max},\ \max\Big\{0,\ -\frac{1}{2 B_i} \sum_m \lambda_m(t) \frac{\partial f_m}{\partial u_i}(x^*(t)) \Big\} \Big\}.$$

For a control moving individuals from compartment $p$ to compartment $q$ at per-capita rate $u_i$ (e.g. vaccinating susceptibles $S \to V$, or treating hospitalized $H \to R$), $\partial f_p/\partial u_i = -x_p$ and $\partial f_q/\partial u_i = +x_p$, so

$$u_i^* = \min\Big\{ u_i^{\max},\ \max\Big\{0,\ \frac{(\lambda_p - \lambda_q)\, x_p}{2 B_i}\Big\}\Big\}.$$

The state equations forward in time, the adjoint equations backward in time, and this characterization form the **optimality system**; for small $T$ its solution is unique, which gives uniqueness of the optimal control.

## Expansion

The adjoint $\lambda_m(t)$ is the marginal value, in units of the objective, of one more individual in compartment $m$ at time $t$; the control on a transfer $p \to q$ is applied in proportion to the value gained by moving individuals ($\lambda_p - \lambda_q$), scaled by the size of the source compartment and divided by its cost. Bang–bang or singular arcs, typical with linear costs, are excluded by the strictly convex quadratic cost. Uniqueness for small horizons follows from Lipschitz bounds on the state–adjoint system (a contraction argument on $[0,T]$). Numerically the optimality system is solved by the forward–backward sweep: integrate the state forward with the current control, integrate the adjoints backward, update the control by the projection formula, and iterate to convergence.

## Sources

- M. L. Diagne, H. Rwezaura, S. Y. Tchoumi, J. M. Tchuenche, "A Mathematical Model of COVID-19 with Vaccination and Treatment", Computational and Mathematical Methods in Medicine 2021 (2021) 1250129, Section 4 (objective (28), Hamiltonian (30), Theorem 2 with adjoint system (31) and control characterization), <https://doi.org/10.1155/2021/1250129>.
- A. Omame, H. Rwezaura, M. L. Diagne, S. C. Inyama, J. M. Tchuenche, "COVID-19 and dengue co-infection in Brazil: optimal control and cost-effectiveness analysis", The European Physical Journal Plus 136 (2021) 1090, Section 5 (Theorem 5.1), <https://doi.org/10.1140/epjp/s13360-021-02030-6>.
- O. Agossou, M. N. Atchadé, A. M. Djibril, "Modeling the effects of preventive measures and vaccination on the COVID-19 spread in Benin Republic with optimal control", Results in Physics (2021) 104969, Theorems 3–4 (existence of an optimal control and its characterization), <https://doi.org/10.1016/j.rinp.2021.104969>.
- W. H. Fleming, R. W. Rishel, Deterministic and Stochastic Optimal Control, Springer (1975), Chapter III.
