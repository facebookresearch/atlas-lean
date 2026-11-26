# Threshold dynamics and Pontryagin controls for mask wear and screening in an SIRD model

**Model.** Susceptible $S$, infectious $I$, recovered $R$ and dead $D$ individuals evolve as
$$\dot S = \Lambda - u_1\beta SI - \mu S, \qquad \dot I = u_1\beta SI - (u_2 + \mu + \delta)I,$$
$$\dot R = \alpha(u_2 + \delta)I - \mu R, \qquad \dot D = (1 - \alpha)(u_2 + \delta)I,$$
with recruitment $\Lambda$, transmission $\beta$, natural death $\mu$, removal rate $\delta$, recovery fraction $\alpha \in (0,1)$ among removed individuals, and two controls: $1 - u_1 \in [0,1]$ is the probability of mask wear and $u_2 \ge 0$ the screening rate.

**Theorem (constant controls).** The region $\Omega = \{(S, I, R) \in \mathbb{R}_+^3 : S + I + R \le \Lambda/\mu\}$ is positively invariant and attracts nonnegative solutions. With
$$\mathcal{R}_0 = \frac{u_1\beta\Lambda}{\mu(u_2 + \mu + \delta)},$$
the disease-free equilibrium $E_0^* = (\Lambda/\mu, 0, 0)$ is globally asymptotically stable on $\Omega$ if $\mathcal{R}_0 \le 1$, and if $\mathcal{R}_0 > 1$ the endemic equilibrium
$$S^* = \frac{\Lambda}{\mu\mathcal{R}_0}, \qquad I^* = \frac{\Lambda}{u_2 + \mu + \delta}\Big(1 - \frac{1}{\mathcal{R}_0}\Big), \qquad R^* = \frac{\alpha(u_2 + \delta)(\mathcal{R}_0 - 1)}{u_1\beta}$$
is globally asymptotically stable.

**Theorem (optimal control).** For time-dependent controls $u_1(t) \in [u_1^{\min}, u_1^{\max}]$, $u_2(t) \in [u_2^{\min}, u_2^{\max}]$, minimize deaths plus screening cost
$$J(u_1, u_2) = A_1 D(t_f) + A_2\int_0^{t_f} u_2(t)^2\,dt = \int_0^{t_f}\Big(A_1(1-\alpha)\big(u_2 + \delta\big)I + A_2u_2^2\Big)dt.$$
An optimal control exists. With adjoints $\lambda_1, \dots, \lambda_4$ satisfying $\dot\lambda = -\partial H/\partial X$ and $\lambda_i(t_f) = 0$, the optimal controls are
$$u_1^* = \begin{cases}u_1^{\min}, & \lambda_2 - \lambda_1 > 0,\\ u_1^{\max}, & \lambda_2 - \lambda_1 < 0,\end{cases} \qquad u_2^* = \min\Big\{u_2^{\max},\ \max\Big\{u_2^{\min},\ \frac{(\lambda_2 - (1-\alpha)A_1)\,I}{2A_2}\Big\}\Big\}.$$

## Expansion

Positivity and the bound on $N = S + I + R$ follow from $\dot N \le \Lambda - \mu N$. $\mathcal{R}_0$ comes from the next-generation operator $F = u_1\beta SI$, $V = (u_2 + \mu + \delta)I$ at the disease-free state; global stability uses quadratic and Volterra-type Lyapunov functions. In the control problem the Hamiltonian is linear in $u_1$, so mask wear is bang–bang, switching on the sign of $\lambda_2 - \lambda_1$ (the shadow value of moving a susceptible into the infectious class), while the quadratic screening cost gives an interior, clipped feedback in $u_2$. Existence follows from convexity of the integrand in $u_2$, compact control sets and a priori bounds on the state (the Fleming–Rishel existence theorem).

## Sources

- A. Bouhali, W. Ben Aribi, S. Ben Miled and A. Kebir, "Optimal Control applied to SIRD model of COVID 19", arXiv:2109.01457 (2021), model (Section 2), Theorems 2.1 and 2.2 (Section 2.1), objective functional and Theorems 3.1 and 3.2 (Section 3), <https://doi.org/10.48550/arXiv.2109.01457>.
