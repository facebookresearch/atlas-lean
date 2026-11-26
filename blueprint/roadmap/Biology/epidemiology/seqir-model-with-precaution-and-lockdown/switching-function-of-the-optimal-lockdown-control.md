# Switching function of the optimal lockdown control

For the system

$$\begin{aligned}
S' &= A - kSE + b_1 Q - dS - pMS, \\
E' &= kSE - (b_2 + \alpha + \sigma + d)E, \\
Q' &= b_2 E - (b_1 + c + d)Q, \\
I' &= \alpha E + cQ - (\eta + d + \delta)I, \\
R' &= \eta I + \sigma E - dR + pMS,
\end{aligned}$$

with $k = \beta(1-\rho_1)(1-\rho_2)$, where $A > 0$ is recruitment, $\beta > 0$ the transmission rate, $\rho_1, \rho_2 \in (0,1)$ the precaution fractions of susceptibles and exposed, $b_2, \alpha, \sigma > 0$ the rates from $E$ to quarantine, to hospitalized infection and to recovery, $b_1, c > 0$ the rates from $Q$ back to $S$ and on to $I$, $\eta > 0$ recovery, $d > 0$ natural and $\delta \ge 0$ disease mortality, and $pM \ge 0$ the removal rate of susceptibles by the lockdown policy. Hospitalized individuals ($I$) are isolated and do not transmit.

let the policy intensity $M(t)$ be a Lebesgue-measurable control with $0 \le a \le M(t) \le b < 1$ on $[0, t_f]$, and minimize the cost

$$J(M) \;=\; \int_0^{t_f} \bigl(c_1 I(t) + c_2 M(t)\bigr)\, dt, \qquad c_1, c_2 > 0 .$$

With Hamiltonian $H = c_1 I + c_2 M + \lambda_1 S' + \lambda_2 E' + \lambda_3 Q' + \lambda_4 I' + \lambda_5 R'$, Pontryagin's minimum principle gives adjoints satisfying $\lambda_i' = -\partial H/\partial x_i$ with transversality $\lambda_i(t_f) = 0$; in particular $\lambda_4' = (\eta + d + \delta)\lambda_4 - c_1 - \eta\lambda_5$ and $\lambda_5' = d\lambda_5$, so $\lambda_5 \equiv 0$. Since $H$ is affine in $M$, the optimal control is determined by the switching function

$$\Phi(t) \;=\; \frac{\partial H}{\partial M} \;=\; c_2 + (\lambda_5 - \lambda_1)\,pS \;=\; c_2 - p\,\lambda_1(t)\,S(t):$$

$M^*(t) = b$ where $\Phi(t) < 0$, $M^*(t) = a$ where $\Phi(t) > 0$, and on any interval where $\Phi \equiv 0$ the control is singular and must be found from the vanishing of the successive time derivatives of $\Phi$.

## Depends on

- [Basic reproduction number and endemic equilibrium of the SEQIR model](basic-reproduction-number-and-endemic-equilibrium-of-the-seqir-model.md)

## Expansion

Existence of an optimal control follows from standard results because the state is bounded (total population is attracted to $[0, A/d]$), the control set is convex and compact, and the integrand is convex in $M$. The only place $M$ enters the dynamics is the flow $pMS$ from $S$ to $R$, so $\partial H/\partial M = c_2 - \lambda_1 pS + \lambda_5 pS$. Minimizing an affine function of $M$ over $[a, b]$ selects an endpoint according to the sign of its slope, which gives the bang-bang law. The adjoint $\lambda_1$ is the marginal cost of one more susceptible, so full lockdown is optimal exactly when moving susceptibles to the removed class saves more future infection cost than the policy costs. Because $M$ does not appear in $\dot\Phi$, singular arcs require the second derivative of $\Phi$, in which $M$ appears linearly.

## Sources

- M. Mandal, S. Jana, S. K. Nandi, A. Khatua, S. Adak, T. K. Kar, "A model based study on the dynamics of COVID-19: Prediction and control", *Chaos, Solitons & Fractals* 136 (2020) 109889, Section 4 (Equations (6)–(15)), <https://doi.org/10.1016/j.chaos.2020.109889> (PMC7218394).
