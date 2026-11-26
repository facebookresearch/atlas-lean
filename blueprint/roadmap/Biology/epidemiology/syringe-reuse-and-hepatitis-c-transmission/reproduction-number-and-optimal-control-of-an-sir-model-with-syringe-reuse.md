# Reproduction number and optimal control of an SIR model with syringe reuse

**Model.** Among people who inject drugs, let $S$ be susceptibles who do not reuse syringes, $U$ susceptibles who reuse syringes, $I$ infectious and $R$ recovered individuals, with $N = S + U + I + R$:

$$
\begin{aligned}
\dot S &= \Lambda - \beta\frac{I}{N}S - \eta S + \alpha R + \theta U - \mu S,\\
\dot U &= \eta S - \beta\frac{I}{N}U - \varepsilon\frac{I}{N}U - \theta U - \mu U,\\
\dot I &= \beta\frac{I}{N}(S + U) + \varepsilon\frac{I}{N}U - (\gamma + \mu) I,\\
\dot R &= \gamma I - (\alpha + \mu) R .
\end{aligned}
$$

All parameters are positive: recruitment $\Lambda$, mortality $\mu$, direct transmission $\beta$, additional syringe-mediated transmission $\varepsilon$ for reusers, adoption $\eta$ and cessation $\theta$ of syringe reuse, recovery $\gamma$ and waning immunity $\alpha$. Then $\dot N = \Lambda - \mu N$, the region $\{N \le \Lambda/\mu\}$ of the non-negative orthant is positively invariant, and solutions are unique, global, non-negative and bounded.

**Threshold.** At the disease-free equilibrium the reusers form the fraction $U_0/N_0 = \eta/(\eta + \theta + \mu)$, and the next-generation method gives

$$
\mathcal{R}_0 = \frac{\beta}{\gamma + \mu} + \frac{\varepsilon\,\eta}{(\eta + \theta + \mu)(\gamma + \mu)} .
$$

The disease-free equilibrium is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$. A unique endemic equilibrium with $I^* > 0$ exists if and only if $\mathcal{R}_0 > 1$, and it is then locally asymptotically stable. The equilibria exchange stability in a transcritical bifurcation at $\mathcal{R}_0 = 1$.

**Optimal control.** Interventions $u_1, u_2 \in [0,1]$ reduce adoption ($\eta \to \eta(1 - u_1)$) and accelerate cessation ($\theta \to \theta(1 + u_2)$). To minimize

$$
J(u_1, u_2) = \int_0^T \big(C_I I + C_U U + C_{u_1} u_1^2 + C_{u_2} u_2^2\big)\,\mathrm{d}t ,
$$

an optimal pair must satisfy, with adjoint variables $\lambda_k$ solving $\dot\lambda_k = -\partial\mathcal{H}/\partial k$, $\lambda_k(T) = 0$ for $k \in \{S, U, I, R\}$,

$$
u_1^* = \min\Big\{1, \max\Big\{0, \frac{\eta S^*(\lambda_U - \lambda_S)}{2C_{u_1}}\Big\}\Big\}, \qquad u_2^* = \min\Big\{1, \max\Big\{0, \frac{\theta U^*(\lambda_U - \lambda_S)}{2C_{u_2}}\Big\}\Big\} .
$$

## Expansion

There is a single infected compartment, so the next-generation matrix is the scalar new-infection rate $\beta + \varepsilon U_0/N_0$ per infective, multiplied by the mean infectious period $1/(\gamma + \mu)$. The second term of $\mathcal{R}_0$ is linear in $\varepsilon$ but saturates in the adoption rate $\eta$, because it is limited by the mean time $1/(\eta + \theta + \mu)$ spent as a reuser. At the endemic equilibrium the Jacobian factors as $(\lambda + \alpha + \mu)$ times a $3\times 3$ block for $(S, U, I)$. Local stability follows from Routh-Hurwitz: the coefficients are positive for $\mathcal{R}_0 > 1$, and the Hurwitz determinant is positive near the bifurcation and never vanishes in the endemic region. The optimality conditions come from Pontryagin's maximum principle: $\partial\mathcal{H}/\partial u_i = 0$ gives the interior controls, which are projected onto $[0,1]$. A practical consequence is that syringe programs alone cannot eliminate infection when direct transmission alone exceeds the threshold, $\beta > \gamma + \mu$.

## Sources

- Mohammad Zaman, Emel Khan, Ishfaq Ahmad and Hiromi Seno, "Syringe reuse in HCV transmission among people who inject drugs: behavioral thresholds and optimal control", arXiv (2026), Section 2 (model), Theorems 3.1–3.3 (invariance, positivity, global existence), Section 4 and Theorem 4.1 (basic reproduction number, disease-free stability), Theorems 5.1–5.2 (endemic equilibrium), Proposition 7.1 (optimal controls), <https://doi.org/10.48550/arXiv.2611.33222>.
