# Stationary distribution and extinction of a stochastic SAIRS model with saturated incidences

**Model.** Let $S, A, I, R$ be susceptible, asymptomatic, symptomatic and recovered individuals, driven by independent Brownian motions $B_1,\dots,B_4$ with intensities $\sigma_i$:

$$\begin{aligned}
dS &= \Big[\Lambda - \Big(\frac{\beta_I I}{1+bI} + \frac{\beta_A A}{1+bA}\Big)S - \mu S + \gamma R\Big]dt + \sigma_1 S\,dB_1,\\
dA &= \Big[\Big(\frac{\beta_I I}{1+bI} + \frac{\beta_A A}{1+bA}\Big)S - (\alpha + \delta_A + \mu)A\Big]dt + \sigma_2 A\,dB_2,\\
dI &= [\alpha A - (\delta_I + \mu + d)I]dt + \sigma_3 I\,dB_3,\qquad dR = [\delta_A A + \delta_I I - (\gamma + \mu)R]dt + \sigma_4 R\,dB_4,
\end{aligned}$$

with positive parameters ($\alpha$: progression to symptoms; $\delta_A, \delta_I$: recovery; $d$: disease death; $b$: saturation). Set $m = 4\mu + \alpha + \delta_A + \delta_I + d + \gamma + \tfrac12\sum_{i=1}^4 \sigma_i^2$, $\beta = \min\{\beta_I, \beta_A\}$ and

$$R_0^s = \frac{3}{m}\sqrt[3]{\Lambda\alpha\beta}.$$

**Theorem (persistence in mean).** If $R_0^s > 1$, then for every positive initial value the time averages $\frac1t\int_0^t S$, $\frac1t\int_0^t A$, $\frac1t\int_0^t I$ and $\frac1t\int_0^t R$ have positive lower limits, each bounded below by an explicit positive multiple of $R_0^s - 1$.

**Theorem (ergodic stationary distribution).** If $R_0^s > 1$, the solution has a unique stationary distribution, and it is ergodic.

**Theorem (extinction).** Let $\bar\beta = \max\{\beta_I, \beta_A\}$ and $h = \min\{\mu + \delta_A + \sigma_2^2/2,\ \mu + \delta_I + d + \sigma_3^2/2\}$. If $\bar\beta\Lambda/\mu - h/2 < 0$, then $S(t) \to \Lambda/\mu$ and $A(t), I(t), R(t) \to 0$.

**Optimal control.** Adding two time-dependent controls to the system with a cost functional $J(u)$, there is an admissible optimal control $u^* = (u_1^*, u_2^*)$ with $J(u) \ge J(u^*)$ for all admissible $u$; it is computed from a Pontryagin-type minimum principle with a Hamiltonian and two adjoint vectors.

## Expansion

Persistence uses a Lyapunov function combining logarithms of $S$, $A$, $I$ with linear terms; Itô's formula and the inequality $a + b + c \ge 3\sqrt[3]{abc}$ produce the drift bound $LV_1 \le -m(R_0^s - 1) + (\text{linear terms})$, whose time average yields the lower bounds. Khasminskii's criterion (a compact set outside which a Lyapunov function has negative generator) then gives existence and ergodicity of the stationary law. Extinction follows from Itô's formula for $\ln(A + I)$, whose drift is negative under the stated condition, so $A + I$ decays exponentially.

## Sources

- X. Zhang, Z. Li, S. Chen, J. Yang, "Dynamical behavior and optimal control of a stochastic SAIRS epidemic model with two saturated incidences", arXiv:2405.09982 (2024), model (2), Theorems 1–3 (Section 3) and Theorem 4 (Section 4), <https://doi.org/10.48550/arXiv.2405.09982>.
