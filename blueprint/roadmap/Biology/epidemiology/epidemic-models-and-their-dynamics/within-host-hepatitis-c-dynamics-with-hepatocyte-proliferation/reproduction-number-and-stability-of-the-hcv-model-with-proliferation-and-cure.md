# Reproduction number and stability of the HCV model with hepatocyte proliferation and cure

**Setting.** Healthy hepatocytes $T$, infected hepatocytes $I$ and free virions $V$ of hepatitis C virus evolve under therapy as

$$\dot T = s + r_T T\Big(1 - \frac{T+I}{T_{max}}\Big) - d_T T - (1-\eta)\beta VT + qI,$$

$$\dot I = r_I I\Big(1 - \frac{T+I}{T_{max}}\Big) + (1-\eta)\beta VT - d_I I - qI, \qquad \dot V = (1-\varepsilon)pI - cV,$$

where both cell types proliferate logistically up to the liver capacity $T_{max}$, infected cells are cured (non-cytolytically) at rate $q$, and therapy blocks new infections with efficacy $\eta$ and virion production with efficacy $\varepsilon$. Write $\delta = d_I + q$ and $1 - \theta = (1-\varepsilon)(1-\eta)$; all parameters are positive.

**Theorem.**
1. (Well-posedness, Theorems 2.1–2.4 and 3.1) Solutions with positive initial data stay positive, exist for all $t \ge t_0$, and are bounded; the region $\{0 < T + I \le \tilde T_0,\ 0 < V \le \lambda_0\}$ with explicit $\tilde T_0$ and $\lambda_0 = \max\{V_0, (1-\varepsilon)p\tilde T_0/c\}$ is positively invariant.
2. (Infection-free state and $\mathcal R_0$, Propositions 2.6 and 2.8) The uninfected equilibrium is $E^0 = (T^0, 0, 0)$ with

$$T^0 = \frac{T_{max}}{2r_T}\Big(r_T - d_T + \sqrt{(r_T - d_T)^2 + \frac{4r_T s}{T_{max}}}\Big),$$

and the basic reproduction number is

$$\mathcal R_0 = \frac{r_I}{d_I + q}\Big(1 - \frac{T^0}{T_{max}}\Big) + \frac{(1-\theta)\beta pT^0}{c(d_I + q)}.$$

3. (Equilibria and local stability, Theorems 3.14, 3.15 and 3.18) There is a unique infected equilibrium $E^*$, given in closed form, if and only if $\mathcal R_0 > 1$. $E^0$ is locally asymptotically stable if $\mathcal R_0 \le 1$ and unstable if $\mathcal R_0 > 1$; for $\mathcal R_0 > 1$, $E^*$ is locally asymptotically stable when a Routh–Hurwitz quantity $\Delta_2$ is positive.
4. (Global stability, Theorems 3.20–3.21) $E^0$ is globally asymptotically stable if $\mathcal R_0 < 1 - q/\delta$. If $r_I = r_T$, $s = d_T T_{max}$ and $\delta = d_T$, then $E^*$ is globally asymptotically stable whenever it exists.

## Expansion

$\mathcal R_0$ has two additive parts because an infected hepatocyte reproduces infection in two ways: by dividing into infected daughter cells, at net per-capita rate $r_I(1 - T^0/T_{max})$ in the uninfected liver, and by releasing $(1-\varepsilon)p/c$ virions over its lifetime, each infecting $(1-\eta)\beta T^0$ cells per unit time; dividing by the removal rate $d_I + q$ gives the expected number of secondary infected cells. Both drug efficacies act only on the viral route, so when infected-cell proliferation alone exceeds removal, therapy cannot push $\mathcal R_0$ below one, which is why proliferation of infected cells matters for treatment success. Local stability of $E^0$ follows from the next-generation decomposition and the Jacobian, global stability from a Lyapunov function, and the closed form of $E^*$ from reducing the steady-state equations to a quadratic in $T$.

## Sources

- Alexis Nangue, Cyprien Fokoue and Raoue Poumeni, "Mathematical analysis of an extended cellular model of the hepatitis C virus infection with non-cytolytic process", arXiv:1905.02561 (2019), Section 2 (model and Theorems 2.1–2.4, Propositions 2.6 and 2.8), Section 3 (Theorems 3.1, 3.14, 3.15, 3.18, 3.20 and 3.21), <https://doi.org/10.48550/arXiv.1905.02561>. Published version: Journal of Applied Mathematics and Physics 7 (2019) 1531–1546, <https://doi.org/10.4236/jamp.2019.77104>.
