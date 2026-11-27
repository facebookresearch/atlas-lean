# Pulse-vaccination bifurcation diagram for an SI model with logistic susceptibles

**Model.** Susceptibles $S$ grow logistically and infectives $I$ are removed at rate $\sigma + g$ (disease mortality plus recovery); every $T > 0$ time units a fraction $p \in [0,1]$ of the susceptibles is vaccinated:

$$\dot S = S(A - S) - \beta_\gamma(t)\,IS, \qquad \dot I = \beta_\gamma(t)\,IS - (\sigma + g)I \qquad (t \ne nT),$$

$$S(nT) = (1-p)\,S(nT^-), \qquad I(nT) = I(nT^-),$$

with $A \in (0,1]$, $\beta_\gamma(t) = \beta_0\big(1 + \gamma\Psi(\omega t)\big)$ and $\Psi$ periodic (seasonal forcing). Let $S_c = (\sigma + g)/\beta_0$ be the critical susceptible level and $\mathcal R_0 = A\beta_0/(\sigma + g) = A/S_c$.

**Theorem (no seasonality, $\gamma = 0$, $A > S_c$).** Define

$$p_1(T) = 1 - e^{-AT}, \qquad p_2(T) = 1 - e^{-(A - S_c)T}, \qquad 0 < p_2(T) < p_1(T).$$

1. If $p \in (p_1(T), 1]$, every solution converges to the trivial periodic solution $(S,I) = (0,0)$.
2. If $p \in (p_2(T), p_1(T))$, every solution with $S_0 > 0$ converges to a nontrivial disease-free periodic solution $(\mathcal S, 0)$.
3. If $p \in (0, p_2(T))$, the system is permanent and every solution with $S_0, I_0 > 0$ converges to an endemic periodic solution $(\mathcal S, \mathcal I)$; for $p = 0$ it converges to the endemic equilibrium.
4. The curves $p = p_1(T)$ and $p = p_2(T)$ are saddle-node and transcritical bifurcation curves, respectively.
5. The basic reproduction number of the pulsed system is

$$\mathcal R_p = \mathcal R_0\Big[\frac{\ln(1-p)}{AT} + 1\Big],$$

and $\mathcal R_p > 1$ if and only if $p < p_2(T)$.

**Corollary (weak seasonality).** For $\gamma, \omega > 0$ small, the disease-free periodic solution $(\mathcal S, 0)$ is asymptotically stable if and only if $p_2^{\mathrm{seas}}(T) < p < p_1(T)$, where

$$p_2^{\mathrm{seas}}(T) = 1 - \exp\Big[-\Big((A - S_c)T + \gamma\int_0^T \Psi(\omega t)\,\mathcal S(t)\,dt\Big)\Big].$$

**Theorem (chaos under strong seasonality).** If $0 < p < p_2^{\mathrm{seas}}(T)$, $T$ is an integer multiple of the forcing period, and $\gamma$ is large enough, the flow has a suspended topological horseshoe; in particular it has infinitely many periodic solutions and positive topological entropy.

## Expansion

Between pulses the disease-free subsystem is the logistic equation, solvable in closed form, so the stroboscopic (period-$T$) map of $S$ is explicit; its nontrivial fixed point exists iff $(1-p)e^{AT} > 1$, i.e. $p < p_1(T)$, giving the saddle-node curve. Linearizing the $I$ equation along $(\mathcal S, 0)$ gives the Floquet multiplier $\exp\big(\int_0^T (\beta_0 \mathcal S(t) - (\sigma+g))\,dt\big)$, and $\int_0^T \mathcal S\,dt = AT + \ln(1-p)$ from the logistic equation; the multiplier crosses $1$ exactly on $p = p_2(T)$, which is also where $\mathcal R_p = 1$. Global convergence uses monotonicity of the stroboscopic map and permanence estimates. For large $\gamma$ the forced system develops stretching and folding in the stroboscopic map, and a horseshoe in the first-return map follows.

## Sources

- João P. S. Maurício de Carvalho, Alexandre A. Rodrigues, "Pulse vaccination in a SIR model: global dynamics, bifurcations and seasonality", arXiv (2023). Section 3 (model and $S_c$, $\mathcal R_0$), Theorem A, Corollary 1, Theorem B, Proposition 3, Corollary 2. <https://doi.org/10.48550/arXiv.2312.02306>. Published version: Communications in Nonlinear Science and Numerical Simulation 139 (2024), article 108272, <https://doi.org/10.1016/j.cnsns.2024.108272>; locators above refer to the arXiv version.
