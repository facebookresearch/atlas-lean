# Reproduction number and backward bifurcation of a leaky-vaccine COVID-19 model with asymptomatic and isolated classes

**Model.** The population $N$ is split into susceptible $S$, vaccinated $V$, unvaccinated asymptomatic $A$ and symptomatic $I$ infectives, vaccinated asymptomatic $A_1$ and symptomatic $I_1$ infectives, isolated $Q$ and recovered $R$. With force of infection

$$\lambda = \beta\,\frac{I + \nu A + \nu_1 A_1 + \kappa I_1}{N},$$

recruitment $\Lambda$, natural death $\mu$, vaccination rate $\sigma$, vaccine efficacy $\rho$ (vaccinated individuals are infected at rate $(1-\rho)\lambda$), loss of immunity at rate $\omega$ (a part $\varphi$ to $S$, the rest to $V$), asymptomatic fractions $\eta, \phi$, isolation rates $\theta, \theta_1, \epsilon, \epsilon_1$, recovery rates $\gamma_i$ and disease death rates $\delta, \delta_1$:

$$\begin{aligned} S' &= \Lambda - (\lambda + \sigma + \mu)S + \varphi R, \qquad V' = \sigma S - \big((1-\rho)\lambda + \mu\big)V + (\omega - \varphi)R, \\ A' &= \eta\lambda S - k_1 A, \qquad I' = (1-\eta)\lambda S - k_2 I, \\ A_1' &= \phi(1-\rho)\lambda V - k_3 A_1, \qquad I_1' = (1-\phi)(1-\rho)\lambda V - k_4 I_1, \\ Q' &= \theta A + \theta_1 A_1 + \epsilon I + \epsilon_1 I_1 - (\gamma_3 + \delta + \mu)Q, \qquad R' = \gamma_1 A + \gamma_2 I + \gamma_3 Q + \gamma_4 A_1 + \gamma_5 I_1 - (\omega + \mu)R, \end{aligned}$$

with $k_1 = \theta + \gamma_1 + \mu$, $k_2 = \epsilon + \gamma_2 + \delta + \mu$, $k_3 = \theta_1 + \gamma_4 + \mu$, $k_4 = \epsilon_1 + \gamma_5 + \delta_1 + \mu$.

**Reproduction number.** The next-generation method gives

$$\mathcal R_0 = \frac{\nu\,\eta\,\beta\mu}{(\sigma+\mu)k_1} + \frac{(1-\eta)\beta\mu}{(\sigma+\mu)k_2} + \frac{\nu_1\phi(1-\rho)\beta\sigma}{(\sigma+\mu)k_3} + \frac{\kappa(1-\phi)(1-\rho)\beta\sigma}{(\sigma+\mu)k_4},$$

the sum of the contributions of the four infectious classes; for a perfect vaccine with permanent immunity ($\rho = 1$, $\omega = 0$) only the first two terms remain.

**Theorem.**

1. The region $\{0 \le N \le \Lambda/\mu\}$ of the nonnegative orthant is positively invariant; the disease-free equilibrium is locally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$.
2. Depending on the signs of the coefficients of the polynomial equation for the endemic force of infection, there is a unique endemic equilibrium when $\mathcal R_0 > 1$ in most parameter cases, but multiple endemic equilibria can coexist for $\mathcal R_0 < 1$; the model undergoes a **backward bifurcation** at $\mathcal R_0 = 1$.
3. If $\rho = 1$ and $\omega = 0$, the disease-free equilibrium is globally asymptotically stable for $\mathcal R_0 < 1$, and the endemic infectious level is strictly smaller with vaccination: $I^*(\sigma) < I^*(0)$ for $\sigma > 0$.

So with a leaky vaccine, pushing $\mathcal R_0$ just below $1$ need not eliminate the disease, whereas with a perfect, durable vaccine the threshold is sharp and vaccination monotonically lowers endemic prevalence.

## Expansion

At the disease-free equilibrium $S_0 = \Lambda/(\sigma + \mu)$ and $V_0 = \sigma\Lambda/(\mu(\sigma+\mu))$, so a fraction $\mu/(\sigma+\mu)$ of the population is unvaccinated and $\sigma/(\sigma+\mu)$ vaccinated; each term of $\mathcal R_0$ is (transmission into the class) $\times$ (relative infectiousness) $\times$ (mean time in the class). Writing the endemic state in terms of $\lambda^*$ reduces equilibria to a polynomial equation whose coefficient sign patterns give the cases in item 2, and the Castillo-Chavez–Song center-manifold theorem (Theorem 4.1 of their 2004 paper) shows the bifurcation at $\mathcal R_0 = 1$ is backward. For $\rho = 1$, $\omega = 0$ vaccinated individuals leave the transmission chain, which yields global stability of the disease-free state and lets one compare the endemic equilibria with and without vaccination directly.

## Sources

- Tesfalem Abate Tegegn, Yibeltal Adane Terefe, "Contribution of the 2021 COVID-19 Vaccination Regime to COVID-19 Transmission and Control in South Africa: A Mathematical Modeling Approach", arXiv (2023). Section 2 (model, force of infection), Section 3 ($\mathcal R_0$; Theorems 3.1, 3.4, 3.5, 3.7, 3.8, 3.10). <https://doi.org/10.48550/arXiv.2311.18369>. Published version: Chaos, Solitons & Fractals 199 (2025), article 116870, <https://doi.org/10.1016/j.chaos.2025.116870>; locators above refer to the arXiv version.
