# Neural-network controls and Pontryagin conditions for cancer immunotherapy

**Tumor–immune model.** Cancer cells $C$, tumor antigen $A$, inflammatory signal $I$, effector T cells $E$ and non-effector T cells $S$ evolve as

$$C' = F(C)C - \kappa CE, \quad A' = r_AC - \delta_AA, \quad I' = r_ICE - \delta_II,$$

$$E' = -r_E(E - E^*) + u_1\beta AIES - u_2\gamma ES, \qquad S' = -r_S(S - S^*) - u_1\beta AIES + u_2\gamma ES,$$

with capped logistic growth $F(C) = \min\{r_{\max}, r_C(1 - C/C^*)\}$. The control $u_1 \in [m_1,M_1]$ scales co-stimulation (activation of non-effector into effector cells) and $u_2 \in [m_2,M_2]$ scales co-suppression (checkpoint-type reversion of effectors); doses are $v_1 = u_1 - m_1$ and $v_2 = M_2 - u_2$. Therapy minimizes

$$J(u_1,u_2) = \int_0^{t_f}\big(aC - bE + cS + c_1v_1^2 + c_2v_2^2\big)\,dt + d_1C(t_f) - d_2E(t_f) + d_3S(t_f).$$

A chemotherapy extension multiplies tumor growth by $u_3$ and boosts antigen presentation and inflammation by $1 + e\tanh(-\ln u_3)$ (immunogenic cell death).

**Neural-network parametrization.** For a general problem $\min\int_{t_0}^{t_1}f(t,y,u)\,dt$ subject to $y' = g(t,y,u)$, $y(t_0) = y_0$ with $C^1$ data, write $u(t) = \mathrm{NN}(t,p)$ (box constraints imposed by a tanh output layer and an affine rescaling), so the problem becomes minimizing $\mathcal{L}(p)$ over network weights $p \in \mathbb{R}^s$, a universal differential equation. With $\lambda$ solving the adjoint equation $\lambda_i' = -\partial_{y_i}(f + \lambda\cdot g)$ and $\lambda(t_1) = 0$, the gradient is

$$\frac{\partial\mathcal{L}}{\partial p_r} = \int_{t_0}^{t_1}\Big(\frac{\partial f}{\partial p_r} + \lambda(t)\cdot\frac{\partial g}{\partial p_r}\Big)\,dt = \int_{t_0}^{t_1}\frac{\partial H}{\partial p_r}\,dt, \qquad H = f + \lambda\cdot g.$$

**Theorem (Section 3.3).** At a stationary parameter $p^*$, the control $u^* = \mathrm{NN}(\cdot,p^*)$ and state $y^* = y(\cdot,p^*)$ admit a piecewise differentiable adjoint $\lambda$ satisfying the adjoint equation and the transversality condition $\lambda(t_1) = 0$, for which the Pontryagin optimality condition holds within the class of network-representable controls.

## Expansion

The identity above is the continuous adjoint method: adding $\int\frac{d}{dt}(\lambda\cdot y)\,dt$ and choosing $\lambda$ to annihilate the $\partial y/\partial p_r$ terms removes all state sensitivities, so the backward sweep of the forward–backward method is replaced by reverse-mode differentiation through the ODE solver. Stationarity $\nabla_p\mathcal{L}(p^*) = 0$ gives $\int\partial_{p_r}H\,dt = 0$ for every weight, the parametric form of the first-order condition $\partial_uH = 0$; the source states the pointwise version (Hamiltonian extremal among network controls), which requires the network family to be rich enough to localize variations in time. Numerically, for a parameter set where the uncontrolled tumor does not respond, the optimized schedules front-load co-stimulation and checkpoint blockade, and low-dose chemotherapy preconditioning improves the immune response.

## Sources

- Wenjing Zhang, Wandi Ding and Huaiping Zhu, *Universal differential equations for optimal control problems and its application on cancer therapy*, arXiv:2504.16035 (2025). <https://doi.org/10.48550/arXiv.2504.16035> Section 3 (UDE formulation, adjoint gradient, necessary conditions and theorem) and Section 4 (tumor–immune model, objective and chemotherapy extension).
