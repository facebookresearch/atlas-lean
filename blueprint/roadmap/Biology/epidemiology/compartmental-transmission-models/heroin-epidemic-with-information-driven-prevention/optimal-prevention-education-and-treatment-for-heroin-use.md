# Optimal prevention education and treatment for heroin use

In the heroin epidemic model with information-driven prevention (susceptibles $S$, untreated users $U_1$, treated users $U_2$, educated $E$, information density $Z$), replace the information-response intensity by a control $u_1(t) \in [0, u_{1\max}]$ (prevention education) and the treatment-entry rate $p$ by a control $u_2(t) \in [0, u_{2\max}]$ (case holding), both Lebesgue measurable on $[0, t_f]$:

$$ \dot U_1 = \beta_1 S U_1 - u_2 U_1 + \beta_2 U_1 U_2 - (\mu + \delta_1) U_1, \qquad \dot U_2 = u_2 U_1 - \beta_2 U_1 U_2 - (\mu + \delta_2) U_2, $$

$$ \dot S = \Lambda - \beta_1 S U_1 - \mu S + \theta E - u_1 \rho S Z, \qquad \dot E = u_1 \rho S Z - (\mu + \theta) E, \qquad \dot Z = \frac{a U_1}{1 + b U_1} - a_0 Z. $$

Minimize

$$ J[u_1, u_2] = \int_0^{t_f} \bigl( B_1 U_1 + B_2 u_1^4 + B_3 u_2^2 \bigr)\, dt, $$

with positive weights $B_1, B_2, B_3$ and positive bounds $u_{1\max}, u_{2\max}$.

**Theorem 4.1 (existence).** There is an optimal control pair $(u_1^*, u_2^*)$ minimizing $J$ over the admissible controls.

**Theorem 4.2 (characterization).** Let $(u_1^*, u_2^*)$ be optimal with state $(S^*, U_1^*, U_2^*, E^*, Z^*)$. Then there are adjoint variables $\lambda = (\lambda_1, \dots, \lambda_5)$ (associated with $S, U_1, U_2, E, Z$) solving the adjoint system $\dot\lambda = -\partial H / \partial (S, U_1, U_2, E, Z)$ of the Hamiltonian $H = B_1 U_1 + B_2 u_1^4 + B_3 u_2^2 + \lambda \cdot (\text{right-hand side})$, with transversality conditions $\lambda_i(t_f) = 0$, and

$$ u_1^*(t) = \min\Bigl\{ \max\Bigl\{ 0, \Bigl( \frac{\rho S^*(t) Z^*(t)}{4 B_2} \bigl(\lambda_1(t) - \lambda_4(t)\bigr) \Bigr)^{1/3} \Bigr\}, u_{1\max} \Bigr\}, \qquad u_2^*(t) = \min\Bigl\{ \max\Bigl\{ 0, \frac{(\lambda_2(t) - \lambda_3(t)) U_1^*(t)}{2 B_3} \Bigr\}, u_{2\max} \Bigr\}. $$

## Depends on

- [Heroin epidemic model with information-driven prevention and its reproduction-number threshold](heroin-epidemic-model-with-information-and-its-threshold.md)

## Expansion

Existence follows from the Fleming-Rishel conditions: the state is bounded on the invariant region, the admissible set is closed and convex, the dynamics are linear in the controls, and the integrand is convex in $(u_1, u_2)$ and bounded below by $c(|u_1|^4 + |u_2|^2) - c'$. Pontryagin's maximum principle gives the adjoint system and, on the interior of the control set, the stationarity conditions $4 B_2 u_1^3 = \rho S Z (\lambda_1 - \lambda_4)$ and $2 B_3 u_2 = (\lambda_2 - \lambda_3) U_1$, since education moves individuals from $S$ to $E$ and treatment moves them from $U_1$ to $U_2$; projecting onto the control bounds gives the formulas. Numerically, combining both controls reduces drug users most at the lowest cost.

## Sources

- P. T. Sowndarrajan, L. Shangerganesh, A. Debbouche, D. F. M. Torres, "Optimal control of a heroin epidemic mathematical model", Optimization 71 (2022), 3107–3131, <https://doi.org/10.1080/02331934.2021.2009823>. Published version of arXiv:2111.05906, cited next; locators there refer to the arXiv version.
- Puthur Thangaraj Sowndarrajan, Lingeshwaran Shangerganesh, Amar Debbouche, Delfim F. M. Torres, "Optimal control of a heroin epidemic mathematical model", arXiv (2021). Section 4, Theorems 4.1 and 4.2. <https://doi.org/10.48550/arXiv.2111.05906>
