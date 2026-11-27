# Optimal social-distancing and vaccination control in the SVIR model

In the [SVIR model](threshold-dynamics-of-the-svir-model-with-continuous-vaccination.md), let the vaccination rate $u_1(t) \in [0, \bar u_1]$ and a social-restriction level $u_0(t) \in [0, \bar u_0]$ be controls. Restrictions lower transmission through a decreasing function $\beta(u_0)$, and vaccinated individuals are infected at the reduced rate $\varepsilon\beta(u_0)$:

$$
\begin{aligned}
S' &= -\beta(u_0) S I - u_1 S + \mu - \mu S, \\
V' &= u_1 S - \varepsilon\beta(u_0) V I - \gamma_1 V - \mu V, \\
I' &= \beta(u_0) S I + \varepsilon\beta(u_0) V I - (\gamma + \mu) I,
\end{aligned}
$$

with cost

$$
J(u_0, u_1) = \int_0^T \big[ c(u_0(t)) + c_1 I(t) + c_2 u_1(t)^2 S(t) \big]\, dt .
$$

**Theorem.**

1. (Existence) If $\beta(\cdot)$ is linear and decreasing and $c$ is strictly convex, $C^2$, with $c' > 0$ and $c(0) = 0$, an optimal control exists.
2. (Optimality system) An optimal $(S^*, V^*, I^*, u^*)$ admits adjoint functions $\lambda_1, \lambda_2, \lambda_3$ with $\lambda_i(T) = 0$, solving the Pontryagin adjoint equations, and $u^*(t)$ minimizes the Hamiltonian pointwise.
3. (Quadratic restriction cost) For $\beta(u_0) = \beta_0(1 - u_0)$ and $c(u_0) = b u_0^2$,

$$
u_0^* = \min\Big\{ \max\Big[0, \frac{\beta_0 I^* \big( S^*(\lambda_3 - \lambda_1) + \varepsilon V^*(\lambda_3 - \lambda_2) \big)}{2b} \Big], \bar u_0 \Big\}, \qquad u_1^* = \min\Big\{ \max\Big[0, \frac{\lambda_1 - \lambda_2}{2c_2} \Big], \bar u_1 \Big\}.
$$

Hence $u_0^* \to 0$ as $b \to \infty$, $u_0^* \to \bar u_0$ as $b \to 0$, $u_1^* \to 0$ as $c_2 \to \infty$, and $u_1^* \to \bar u_1$ as $c_2 \to 0$.
4. (Exponential restriction cost) For $c(u_0) = e^{k u_0} - 1$ and $\lambda_3 > \max\{\lambda_1, \lambda_2\}$, $u_0^* = \min\{\max[0, \tfrac1k \ln(\beta_0 I^* K/k)], \bar u_0\}$ with $K = S^*(\lambda_3 - \lambda_1) + \varepsilon V^*(\lambda_3 - \lambda_2)$, and $u_1^*$ is as above.

## Depends on

- [Threshold dynamics of the SVIR model with continuous vaccination](threshold-dynamics-of-the-svir-model-with-continuous-vaccination.md)

## Expansion

Existence follows from the Filippov–Cesari theorem: the state equations are Lipschitz, the control set is compact and convex, the dynamics are affine in $u_1$ and in $\beta(u_0)$, and the integrand is convex in the controls. The Hamiltonian is $H = c(u_0) + c_1 I + c_2 u_1^2 S + \lambda \cdot f$. Setting $\partial H/\partial u_i = 0$ and projecting onto the box gives the explicit formulas. Restrictions pay off when the shadow price of infection $\lambda_3$ exceeds that of the susceptible and vaccinated classes; vaccination pays off when $\lambda_1 > \lambda_2$.

## Sources

- Alessandro Ramponi, Maria Elisabetta Tessitore, "Optimal Social and Vaccination Control in the SVIR Epidemic Model", Mathematics 12 (2024), 933, <https://doi.org/10.3390/math12070933>. Published version of arXiv:2311.15718, cited next; locators there refer to the arXiv version.
- Alessandro Ramponi, M. Elisabetta Tessitore, "Optimal Social and Vaccination Control in the SVIR Epidemic Model", arXiv (2023). Theorem 3, Theorem 5, Proposition 6, Corollary 7, Proposition 8. <https://doi.org/10.48550/arXiv.2311.15718>
