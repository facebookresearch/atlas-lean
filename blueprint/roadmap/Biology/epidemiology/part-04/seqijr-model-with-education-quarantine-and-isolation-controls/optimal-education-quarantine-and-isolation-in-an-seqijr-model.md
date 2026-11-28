# Optimal public-education, quarantine and isolation efforts in an SEQIJR model

**Model.** The population $N = S + E + Q + I + J + R$ consists of susceptible, exposed, quarantined, infectious non-isolated, isolated (hospitalized) and recovered individuals. With recruitment $\Lambda$ (a fraction $\pi$ entering $E$), natural death rate $\mu$, and force of infection

$$\Psi = \frac{\beta (I + \varepsilon_1 E + \varepsilon_2 Q + \varepsilon_3 J)}{N},$$

the state equations with time-dependent controls $\alpha(t)$ (public-health education), $\tau(t)$ (quarantine of exposed) and $\eta(t)$ (isolation of infectious) are

$$\begin{aligned}
S' &= \Lambda(1 - \pi) + q\sigma_1 Q - (1 - \alpha)\Psi S - \mu S, \\
E' &= (1 - \alpha)\Psi S + \Lambda\pi - p\tau E - (1 - p)\rho E - \mu E, \\
Q' &= p\tau E - q\sigma_1 Q - (1 - q)\sigma_2 Q - \mu Q, \\
I' &= (1 - p)\rho E - (\gamma_1 + \eta + d_1 + \mu) I, \\
J' &= (1 - q)\sigma_2 Q + \eta I - (\gamma_2 + d_2 + \mu) J, \\
R' &= \gamma_1 I + \gamma_2 J - \mu R,
\end{aligned}$$

with $p, q, \pi \in [0, 1]$ and positive rates. Admissible controls are Lebesgue measurable with values in $[0, 1]$ on $[0, t_f]$, and the cost is

$$G(\alpha, \tau, \eta) = \int_0^{t_f} \Big( I + \tfrac12 c_1 \alpha^2 + \tfrac12 c_2 \tau^2 + \tfrac12 c_3 \eta^2 \Big) dt, \qquad c_1, c_2, c_3 > 0 .$$

**Theorem (necessary conditions).** Let $H = I + \tfrac12 (c_1\alpha^2 + c_2\tau^2 + c_3\eta^2) + \sum_{x} \lambda_x\, x'$ be the Hamiltonian, the sum running over the six state equations. If $(\alpha^*, \tau^*, \eta^*)$ minimizes $G$ with state $(S, E, Q, I, J, R)$, then there are adjoint functions $\lambda_S, \dots, \lambda_R$ with

$$\lambda_x' = -\frac{\partial H}{\partial x}, \qquad \lambda_x(t_f) = 0,$$

and, for almost every $t$,

$$\alpha^* = \min\Big\{1, \max\Big\{0, \frac{(\lambda_E - \lambda_S)\Psi S}{c_1}\Big\}\Big\}, \quad \tau^* = \min\Big\{1, \max\Big\{0, \frac{(\lambda_E - \lambda_Q) p E}{c_2}\Big\}\Big\}, \quad \eta^* = \min\Big\{1, \max\Big\{0, \frac{(\lambda_I - \lambda_J) I}{c_3}\Big\}\Big\}.$$

## Proof depends on

- [Pontryagin optimality system for epidemic controls with quadratic costs](../optimal-control-of-epidemic-models/pontryagin-optimality-system-with-quadratic-control-costs.md)

## Expansion

The Hamiltonian is strictly convex in each control, and each control enters linearly in the dynamics: $\partial H/\partial\alpha = c_1\alpha + (\lambda_S - \lambda_E)\Psi S$, $\partial H/\partial\tau = c_2\tau + (\lambda_Q - \lambda_E) p E$ and $\partial H/\partial\eta = c_3\eta + (\lambda_J - \lambda_I) I$. Pontryagin's principle requires the controls to minimize $H$ pointwise over $[0, 1]$, which for a convex quadratic is the unconstrained stationary point projected onto the interval. The adjoint equations come from differentiating $H$ in the states (the running cost contributes $-1$ to $\lambda_I'$, and $\Psi$ depends on every state through $N$), and the transversality conditions are zero because there is no terminal cost. Each control is worth applying when the shadow price of moving an individual between the two compartments it couples is positive: education when an extra exposed individual costs more than a susceptible one ($\lambda_E > \lambda_S$), quarantine when $\lambda_E > \lambda_Q$, isolation when $\lambda_I > \lambda_J$.

## Sources

- C. E. Madubueze, S. Dachollom, I. O. Onwubuya, "Controlling the spread of COVID-19: optimal control analysis", *Computational and Mathematical Methods in Medicine* 2020 (2020) 6862516, Section 2 (model (1)–(3)) and Section 4 (cost (32), control set (33), Hamiltonian (35), Theorem 2 with Eqs. (36)–(38)). The source's adjoint system contains typographical slips; here the adjoints are stated as $-\partial H/\partial x$. <https://doi.org/10.1155/2020/6862516> (PMC7499329).
