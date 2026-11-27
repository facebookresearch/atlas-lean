# Reproduction number of a dengue model with fractional-order transmission and recovery

**Model.** Humans are susceptible, infected or recovered ($S_H, I_H, R_H$, total $N_H$ constant, with birth and death rate $\mu_H$). Mosquitoes are susceptible or infected ($S_V, I_V$, recruitment $\Pi_V$, death rate $\mu_V$). Waiting times for transmission and recovery are taken heavy-tailed (power-law, Mittag-Leffler type) rather than exponential. Deriving the mean-field equations from the underlying stochastic process yields Riemann–Liouville fractional derivatives of order $1-\alpha$, $1-\beta$ and $1-p$ ($0 < \alpha \le 1$, $0 < \beta \le p \le 1$), tempered by survival:

$$\begin{aligned} \dot S_H &= \mu_HN_H - \frac{b^\alpha\beta_V^H}{N_H}S_H\,\mathcal D_{\mu_V}^{1-\alpha}[I_V] - \mu_HS_H,\\ \dot I_H &= \frac{b^\alpha\beta_V^H}{N_H}S_H\,\mathcal D_{\mu_V}^{1-\alpha}[I_V] - \frac{1}{C^\beta}\mathcal D_{\mu_H}^{1-\beta}[I_H] - \mu_HI_H,\\ \dot I_V &= \frac{b^p\beta_H^V}{N_HC^p}\,S_V\,\mathcal D_{\mu_H}^{1-p}[I_H] - \mu_VI_V, \end{aligned}$$

with $\dot R_H = C^{-\beta}\mathcal D_{\mu_H}^{1-\beta}[I_H] - \mu_HR_H$ and $\dot S_V = \Pi_V - (\text{infection}) - \mu_VS_V$. Here $\mathcal D_\mu^{\gamma}X = e^{-\mu t}\,{}_{RL}D_t^{\gamma}\bigl[e^{\mu t}X(t)\bigr]$ is a tempered fractional derivative, $b$ is the biting rate, $\beta_V^H$ and $\beta_H^V$ are transmission probabilities, and $C$ is a recovery time scale. Since $S_V + I_V \to \Pi_V/\mu_V$, the system reduces to $(S_H, I_H, I_V)$ on the attracting region $\{S_H + I_H \le N_H,\ I_V \le \Pi_V/\mu_V\}$.

**Approximation and threshold.** For nonnegative continuous $F$ and $\mu > 0$, the paper uses $e^{-\mu t}\,{}_{RL}D_t^{\gamma}[e^{\mu t}F(t)] \approx \mu^{\gamma}F(t)$. The tempered memory terms then act as effective rates: human infection $b^\alpha\beta_V^H\mu_V^{1-\alpha}$, recovery $\mu_H^{1-\beta}/C^\beta$, and mosquito infection $b^p\beta_H^V\mu_H^{1-p}/(N_HC^p)$. The next-generation matrix gives

$$R_0 = \sqrt{\frac{\Pi_V\,b^{\alpha+p}\,\beta_V^H\,\beta_H^V\,C^\beta}{N_H\,C^p\,\mu_V^{1+\alpha}\,\mu_H^{p-\beta}\,\bigl(\mu_H^\beta C^\beta + 1\bigr)}} .$$

**Theorem.** For the reduced fractional dengue system:

1. the disease-free equilibrium is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$, and it is globally asymptotically stable if $R_0 < 1$;
2. a unique endemic equilibrium exists if and only if $R_0 > 1$, with $I_V^* = \frac{\mu_H}{A}(R_0^2 - 1)$ for an explicit constant $A > 0$, and it is then locally and globally asymptotically stable in the interior of the attracting region;
3. an optimal control problem with time-dependent controls on transmission and treatment admits an optimal control, by the standard existence conditions (convex admissible set, dynamics linear in the controls, convex integrand, coercivity).

Memory exponents enter $R_0$ explicitly. With $\alpha = \beta = p = 1$ the classical host–vector value $R_0^2 = \frac{\Pi_Vb^2\beta_V^H\beta_H^V}{N_H\mu_V^2(1/C + \mu_H)}$ is recovered.

## Expansion

In a continuous-time random walk formulation, an individual's transitions are governed by survival functions of power-law type. Conditioning on survival to death (rate $\mu$) produces the factors $e^{\pm\mu t}$, and the memory kernel of a Mittag-Leffler waiting time produces ${}_{RL}D^{1-\gamma}$. The approximation of the tempered derivative by $\mu^{\gamma}$ comes from $\mathcal Le^{-\mu t}\,{}_{RL}D^\gamma(e^{\mu t}F) = (s+\mu)^\gamma\hat F(s)$ evaluated at small $s$. With effective rates in place, the system is a standard Ross–Macdonald model: $R_0^2$ is the product of the mosquito-to-human and human-to-mosquito reproduction numbers. Global stability of the endemic state follows from uniform persistence and the Li–Muldowney geometric (second-compound-matrix) criterion.

## Sources

- Tahajuddin Sk, Kaushik Bal, Santosh Biswas, Tridip Sardar, "Global stability and optimal control in a single-strain dengue model with fractional-order transmission and recovery process", arXiv (2024). Section 2 (Definitions 2.1–2.4, Theorem 2.1), Section 3 (model derivation), Section 4 (Propositions 4.1–4.3), Section 5 (formula for $R_0$, Propositions 5.1–5.4), Section 6 (Theorem 6.1). <https://doi.org/10.48550/arXiv.2402.11974>. Published version: Mathematical Methods in the Applied Sciences 48(15) (2025), 14459–14487, <https://doi.org/10.1002/mma.11191>; locators above refer to the arXiv version.
