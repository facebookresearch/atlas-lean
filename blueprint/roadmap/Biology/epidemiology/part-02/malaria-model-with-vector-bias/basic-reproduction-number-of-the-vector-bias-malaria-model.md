# Basic reproduction number of the vector-bias malaria model

Let $S_h, I_h$ be susceptible and infected humans and $S_v, I_v$ susceptible and infected mosquitoes. With vector-bias parameter $p > 0$ (relative attractiveness of infected humans to mosquitoes), recruitment $\Lambda_h, \Lambda_v$, death rates $\mu_h, \mu_v$, transmission rates $\beta_h$ (mosquito to human) and $\beta_v$ (human to mosquito), natural recovery rate $\delta_0$, extra recovery $\delta_1/(1 + a I_h)$ for the fraction $u_1 \in [0,1]$ of infected humans who are hospitalized (saturating with hospital capacity $a \ge 0$), and fumigation rate $u_2 \ge 0$, the model is

$$
\begin{aligned}
\dot S_h &= \Lambda_h - \beta_h \frac{S_h I_v}{p I_h + S_h} - \mu_h S_h + (1-u_1)\delta_0 I_h + u_1\Big(\delta_0 + \frac{\delta_1}{1 + a I_h}\Big) I_h,\\
\dot I_h &= \beta_h \frac{S_h I_v}{p I_h + S_h} - \mu_h I_h - (1-u_1)\delta_0 I_h - u_1\Big(\delta_0 + \frac{\delta_1}{1 + a I_h}\Big) I_h,\\
\dot S_v &= \Lambda_v - \beta_v \frac{p I_h}{p I_h + S_h} S_v - (\mu_v + u_2) S_v,\\
\dot I_v &= \beta_v \frac{p I_h}{p I_h + S_h} S_v - (\mu_v + u_2) I_v .
\end{aligned}
$$

All parameters are positive except $u_1, u_2, a \ge 0$. The non-negative orthant is invariant, human numbers are eventually bounded by $\Lambda_h/\mu_h$ and mosquito numbers by $\Lambda_v/(\mu_v + u_2)$.

**Proposition.** The disease-free equilibrium is $E_0 = (\Lambda_h/\mu_h, 0, \Lambda_v/(\mu_v+u_2), 0)$, and the next-generation matrix gives

$$R_0 = \sqrt{\frac{p\,\Lambda_v\, \beta_h\, \beta_v\, \mu_h}{\Lambda_h\, (\mu_v + u_2)^2\, (u_1\delta_1 + \delta_0 + \mu_h)}} .$$

$E_0$ is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$. Endemic equilibria correspond to positive roots of a cubic in $I_h$; one always exists when $R_0 > 1$, and for suitable saturation $a$ and vector bias $p$ the system undergoes a backward bifurcation at $R_0 = 1$, so endemic equilibria can coexist with the stable disease-free state when $R_0 < 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)
- [Unstable mode of the infected subsystem exactly when $R_0 > 1$](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)
## Expansion

At $E_0$ the infected subsystem $(I_h, I_v)$ has new-infection matrix $F = \begin{pmatrix} 0 & \beta_h \\ \beta_v p \Lambda_v \mu_h / (\Lambda_h(\mu_v + u_2)) & 0\end{pmatrix}$ (since $S_h I_v/(pI_h + S_h) \approx I_v$ and $p I_h S_v/(p I_h + S_h) \approx p I_h \mu_h \Lambda_v / (\Lambda_h(\mu_v+u_2))$ to first order) and transition matrix $V = \operatorname{diag}(u_1\delta_1 + \delta_0 + \mu_h,\ \mu_v + u_2)$; at $I_h = 0$ the saturated treatment rate equals $\delta_1$. The spectral radius of the anti-diagonal matrix $F V^{-1}$ is the geometric mean of its two entries, the human-to-mosquito and mosquito-to-human reproduction numbers. Larger vector bias $p$ raises $R_0$, while fumigation enters quadratically through $(\mu_v + u_2)^2$ because it shortens both the mosquito lifetime and the mosquito population size.

## Sources

- D. Aldila, M. Angelina, "Optimal control problem and backward bifurcation on malaria transmission with vector bias", Heliyon 7(4) (2021) e06824, system (1), Eqs. (2)–(3), Theorems 1–4, <https://doi.org/10.1016/j.heliyon.2021.e06824>, PMCID PMC8082563.
