# Optimal control of malaria by long-lasting insecticidal net use

**Setting.** In the resting–questing malaria model with long-lasting insecticidal nets, let the effective net coverage $w(t) \in [0,1]$ (the proportion of people owning a net and using it correctly) vary in time. It enters the dynamics through the biting rate $a_{\max} - w\Delta_a$, the vector recruitment $\Lambda_v^{\max} - w\Delta_{\Lambda_v}$, the immunity-loss rate $\gamma_h^{\min} + w\Delta_{\gamma_h}$ and the extra death rate $w\Delta_{\mu_v}$ of questing mosquitoes. Over a horizon $T > 0$, minimize

$$J(w) = \int_0^T \Big[A_1 I_h + A_2\Big(\sum_{i=1}^6 E_q^i + I_q\Big) + B w(t)^2\Big]\,dt$$

over the admissible controls $\Gamma(T) = \{w \text{ Lebesgue measurable on } [0,T],\ 0 \le w(t) \le 1\}$. Here $A_1$ weighs infectious humans, $A_2$ weighs questing infected and infectious mosquitoes, and $B > 0$ is the cost of net use.

**Theorem (existence).** There is $w^* \in \Gamma(T)$ with $J(w^*) = \min\{J(w) : w \in \Gamma(T)\}$.

**Theorem (optimality system).** For an optimal control $w^*$ with state trajectory $\mathbf{x}^*$, there are adjoint variables $\lambda_1, \dots, \lambda_{19}$ satisfying $\lambda_i' = -\partial\mathbb{H}/\partial x_i$ for the Hamiltonian

$$\mathbb{H} = A_1 I_h + A_2\Big(\sum_{i=1}^6 E_q^i + I_q\Big) + Bw^2 + \sum_{i=1}^{19} \lambda_i f_i(\mathbf{x}, w),$$

where $f_i$ is the right-hand side of the $i$-th state equation, with transversality conditions $\lambda_i(T) = 0$. The optimal control is the projection onto $[0,1]$ of the stationary point of $\mathbb{H}$ in $w$:

$$w^*(t) = \max\Big\{0, \min\Big(1, \frac{\Psi(t)}{2B}\Big)\Big\}, \qquad \Psi = -\sum_{i=1}^{19} \lambda_i \frac{\partial f_i}{\partial w}(\mathbf{x}^*, w),$$

where $\Psi$ does not depend on $w$ because every $f_i$ is affine in $w$. In the original variables, $\Psi$ combines the adjoint differences $\lambda_3 - \lambda_1$ weighted by $\Delta_{\gamma_h}R_h^*$, $\lambda_2 - \lambda_1$ weighted by the change in human infection due to reduced biting, $\lambda_5 - \lambda_4$ weighted by the change in mosquito infection, and the adjoints of the questing mosquito classes weighted by $\Delta_{\mu_v}$, together with the term $\Delta_{\Lambda_v}\lambda_4$ from reduced recruitment.

## Depends on

- [Reproduction number and equilibria of the LLIN malaria model](reproduction-number-and-equilibria-of-the-llin-malaria-model.md)

## Expansion

Existence follows from the standard Filippov–Cesari argument: the state is bounded, the admissible set is closed and convex, the dynamics are affine in $w$, and the running cost is convex in $w$ with $Bw^2$ coercive. Pontryagin's maximum principle gives the adjoint system and the condition that $w^*(t)$ minimizes $\mathbb{H}$ over $[0,1]$. Since $\mathbb{H}$ is the strictly convex quadratic $Bw^2 - \Psi w + (\text{terms free of } w)$, the minimizer is $\Psi/(2B)$ clipped to the control bounds. A single net-use control acts on three entomological levers at once (vector density, contact rate and vector longevity), which is why it appears in four parameters of the model.

## Sources

- S. Y. Tchoumi, Y. T. Kouakep, D. J. Fotsa Mbogne, J. C. Kamgang and J. M. Tchuenche, "Optimal control of a malaria model with long-lasting insecticide-treated nets", arXiv:2006.12536 (2020), Section 3: control system, objective functional, Theorem 3.1 (existence of an optimal control) and Theorem 3.2 (adjoint system and characterization of the optimal control). <https://doi.org/10.48550/arXiv.2006.12536>. Published version: Mathematical Modelling and Control 1(4) (2021), 188–207, <https://doi.org/10.3934/mmc.2021018>; locators above refer to the arXiv version.
