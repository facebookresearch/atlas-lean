# Reproduction number of the SEYAR malaria model with exposure-dependent immunity

**Exposure-dependent immunity.** Let $\varepsilon = E/N_H$ be the exposed proportion of humans and $u$ the proportion protected by naturally acquired immunity, rising from $u_{\mathrm{low}}$ toward $u_{\mathrm{high}}$ ($0 \le u_{\mathrm{low}} < u_{\mathrm{high}} < 1$) as exposure accumulates:

$$\dot u = (u_{\mathrm{high}} - u)\,\dot\varepsilon, \qquad u(0) = u_{\mathrm{low}} .$$

Hence $u$ is a function of $\varepsilon$ alone,

$$u(\varepsilon) = u_{\mathrm{high}} + (u_{\mathrm{low}} - u_{\mathrm{high}})\,e^{\varepsilon_0 - \varepsilon}, \qquad \varepsilon_0 = \varepsilon(0),$$

where the initial exposed proportion satisfies $0 \le \varepsilon_0 \le \ln\big(u_{\mathrm{high}}/(u_{\mathrm{high}} - u_{\mathrm{low}})\big)$, so that $u(\varepsilon) \ge 0$ for every $\varepsilon \ge 0$.

**Model.** Humans $S, E, Y$ (symptomatic), $A$ (asymptomatic), $R$ with $N_H = S+E+Y+A+R$, and mosquitoes $M_S, M_E, M_I$:

$$\begin{aligned}
\dot S &= \Omega_H + \lambda_{RS}R - \Big(\sigma\beta_M\frac{M_I}{N_H} + \xi_H\Big)S, &
\dot E &= \sigma\beta_M\frac{M_I}{N_H}S - (\gamma + \xi_H)E,\\
\dot Y &= \gamma\big(1 - u(\varepsilon)\big)E - (\xi_H + \delta + \lambda_{YR})Y, &
\dot A &= \gamma\, u(\varepsilon)\,E - (\lambda_{AR} + \xi_H)A,\\
\dot R &= \lambda_{AR}A + \lambda_{YR}Y - (\lambda_{RS} + \xi_H)R, &
\dot M_S &= \Omega_M - \Big(\xi_M + \sigma\beta_Y\frac{Y}{N_H} + \sigma\beta_A\frac{A}{N_H}\Big)M_S,\\
\dot M_E &= \sigma\Big(\beta_Y\frac{Y}{N_H} + \beta_A\frac{A}{N_H}\Big)M_S - (\xi_M + \tau)M_E, &
\dot M_I &= \tau M_E - \xi_M M_I,
\end{aligned}$$

with biting rate $\sigma$, transmission probabilities $\beta_M$ (mosquito to human), $\beta_Y, \beta_A$ (symptomatic and asymptomatic human to mosquito), recruitment $\Omega_H, \Omega_M$, natural mortalities $\xi_H, \xi_M$, disease death $\delta$, progression rates $\gamma, \tau$ and recovery rates $\lambda_{YR}, \lambda_{AR}$. The disease-free equilibrium is $(\Omega_H/\xi_H, 0,0,0,0, \Omega_M/\xi_M, 0, 0)$.

**Proposition.** With $U_{\mathrm{low}} = u(\varepsilon)|_{\varepsilon = 0} = e^{\varepsilon_0}(u_{\mathrm{low}} - u_{\mathrm{high}}) + u_{\mathrm{high}}$, the asymptomatic share of new infections at the disease-free state (so $0 \le U_{\mathrm{low}} \le u_{\mathrm{low}}$ by the constraint on $\varepsilon_0$), the basic reproduction number is

$$\mathcal R_0 = \sqrt{\frac{\sigma^2\,\tau\,\gamma\,\Omega_M\,\xi_H\,\beta_M}{\xi_M^2(\gamma + \xi_H)(\tau + \xi_M)\,\Omega_H}\left(\frac{\beta_A U_{\mathrm{low}}}{\lambda_{AR} + \xi_H} + \frac{\beta_Y(1 - U_{\mathrm{low}})}{\lambda_{YR} + \xi_H + \delta}\right)},$$

and the disease-free equilibrium is locally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$. Because the bracket adds a non-negative asymptomatic term, setting $\beta_A = 0$ or omitting the $A$ class underestimates $\mathcal R_0$. The stability for $\mathcal R_0 < 1$ is not global in general: a backward bifurcation can create endemic equilibria below threshold unless an auxiliary parameter $\Lambda$ satisfies $\Lambda < 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Since $\dot u = (u_{\mathrm{high}} - u)\dot\varepsilon$ is separable in $\varepsilon$, $\log(u_{\mathrm{high}} - u)$ decreases one-for-one with $\varepsilon$, giving the closed form. In the next-generation matrix at the disease-free state, an infectious mosquito bites at rate $\sigma$ during a mean lifetime $1/\xi_M$ and infects with probability $\beta_M$; an exposed human becomes infectious with probability $\gamma/(\gamma + \xi_H)$, asymptomatic with probability $U_{\mathrm{low}}$ and symptomatic otherwise, and then infects mosquitoes at rate $\sigma\beta_A$ or $\sigma\beta_Y$ (per mosquito, scaled by the vector-to-host ratio $(\Omega_M/\xi_M)/(\Omega_H/\xi_H)$) during mean durations $1/(\lambda_{AR}+\xi_H)$ or $1/(\lambda_{YR}+\xi_H+\delta)$; a fraction $\tau/(\tau+\xi_M)$ of infected mosquitoes survive incubation. The next-generation matrix has the host-to-vector, vector-to-host block form, so $\mathcal R_0$ is the geometric mean of the two one-step reproduction numbers, as in the Ross–Macdonald model. Sensitivity indices of $\mathcal R_0$ are largest for mosquito mortality $\xi_M$ and biting rate $\sigma$.

## Sources

- J. B. Aguilar, J. B. Gutierrez, "An Epidemiological Model of Malaria Accounting for Asymptomatic Carriers", Bulletin of Mathematical Biology 82 (2020) 42, Section 2 (immunity IVP, Eq. 1; SEYAR model, Eq. 4), Section 3 (disease-free equilibrium; Lemma 1, $\mathcal R_0$ Eq. 7 and its factorisation), Section 4.3 (effect of neglecting asymptomatic carriers), Section 5 (backward bifurcation, $\Lambda$ Eq. 10) and Section 7.1 (sensitivity analysis), <https://doi.org/10.1007/s11538-020-00717-y> (PMC7072066).
