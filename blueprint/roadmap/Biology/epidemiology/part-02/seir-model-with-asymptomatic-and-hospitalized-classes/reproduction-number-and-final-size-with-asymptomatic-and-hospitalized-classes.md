# Reproduction number and final size with asymptomatic and hospitalized classes

**Model.** A closed population (no births or background deaths) is split into susceptible $S$, exposed $E$, asymptomatic infectious $I_a$, symptomatic infectious $I_s$, hospitalized or isolated $I_h$ and recovered $R$, with $N = S + E + I_a + I_s + I_h + R$ and

$$\begin{aligned}
\dot S &= -\frac{\beta_a I_a + \beta_s I_s + \beta_h I_h}{N} S, & \dot E &= \frac{\beta_a I_a + \beta_s I_s + \beta_h I_h}{N} S - \sigma E,\\
\dot I_a &= r\sigma E - \gamma_a I_a, & \dot I_s &= (1-r)\sigma E - (\varphi_s + \gamma_s + \delta_s) I_s,\\
\dot I_h &= \varphi_s I_s - (\gamma_h + \delta_h) I_h, & \dot R &= \gamma_a I_a + \gamma_s I_s + \gamma_h I_h,
\end{aligned}$$

where $0 < r \le 1$ is the asymptomatic fraction, $\varphi_s$ the hospitalization (isolation) rate and $\delta_s, \delta_h \ge 0$ disease-induced death rates; all other parameters are positive. Every point $(S^\ast, 0, 0, 0, 0, R^\ast)$ with $0 < S^\ast \le N(0)$ is a disease-free equilibrium (a continuum), with $N^\ast = S^\ast + R^\ast$.

**Theorem.**

1. *(Reproduction number.)* With infected classes ordered $(E, I_a, I_s, I_h)$, $R_0 = \rho(FV^{-1}) = R_a + R_s + R_h$, where

    $$R_a = \frac{\beta_a r}{\gamma_a}\frac{S^\ast}{N^\ast}, \qquad R_s = \frac{\beta_s (1-r)}{\varphi_s + \gamma_s + \delta_s}\frac{S^\ast}{N^\ast}, \qquad R_h = \frac{\beta_h (1-r)\varphi_s}{(\varphi_s + \gamma_s + \delta_s)(\gamma_h + \delta_h)}\frac{S^\ast}{N^\ast}.$$

2. *(Global stability.)* If $R_0 \le 1$ (computed with $S^\ast/N^\ast = 1$), every solution in the invariant region $\{S + E + I_a + I_s + I_h + R \le N(0)\}$ converges to a disease-free equilibrium of the continuum.

3. *(Final size.)* With $S(\infty) = \lim_{t\to\infty} S(t)$ and $R_0$ computed with $S^\ast/N^\ast = 1$,

    $$\ln\frac{S(0)}{S(\infty)} \ \ge\ \frac{R_0}{N(0)}\big(S(0) - S(\infty) + E(0)\big) + \frac{1}{N(0)}\left[\frac{\beta_a}{\gamma_a} I_a(0) + \Big(\beta_s + \frac{\varphi_s\beta_h}{\gamma_h + \delta_h}\Big)\frac{I_s(0)}{\varphi_s + \gamma_s + \delta_s} + \frac{\beta_h}{\gamma_h + \delta_h} I_h(0)\right],$$

    with equality when there is no disease-induced mortality ($\delta_s = \delta_h = 0$).

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

New infections enter only $E$, so $FV^{-1}$ has rank one and $R_0$ is the expected infectiousness of one exposed individual: it becomes asymptomatic with probability $r$ for mean time $1/\gamma_a$, or symptomatic with probability $1-r$ for mean time $1/(\varphi_s+\gamma_s+\delta_s)$, after which it is hospitalized with probability $\varphi_s/(\varphi_s+\gamma_s+\delta_s)$ for mean time $1/(\gamma_h+\delta_h)$. For stability, $L = E + g_1 I_a + g_2 I_s + g_3 I_h$ with $g_1 = \beta_a/\gamma_a$, $g_3 = \beta_h/(\gamma_h+\delta_h)$, $g_2 = (\beta_s + g_3\varphi_s)/(\varphi_s+\gamma_s+\delta_s)$ satisfies $\dot L \le \sigma(R_0 - 1)E$ because $S \le N$; LaSalle's principle gives convergence. For the final size, write the model in the form $\dot x = \Pi\, \beta\, S\, b x - Vx$, $\dot S = -\beta S\, b x$ of Arino, Brauer, van den Driessche, Watmough and Wu, integrate $\dot S / S$ over $[0, \infty)$ and use $\int_0^\infty x\,dt = V^{-1}\big(x(0) + \Pi\,(\text{total new infections})\big)$; the vector $bV^{-1}$ gives the expected remaining infectiousness of an individual in each infected class, which yields the initial-condition terms. Disease deaths make $N$ decrease, so the standard-incidence factor $1/N$ exceeds $1/N(0)$ and only an inequality survives.

## Sources

- A. B. Gumel, E. A. Iboi, C. N. Ngonghala and E. H. Elbasha, "A primer on using mathematics to understand COVID-19 dynamics: Modeling, analysis and simulations", Infectious Disease Modelling 6 (2021), 148–168, Section 2 (model (1), Eqs. (2)–(4), Theorems 2.2 and 2.3), <https://doi.org/10.1016/j.idm.2020.11.005>, PMCID: PMC7786036.
- J. Arino, F. Brauer, P. van den Driessche, J. Watmough and J. Wu, "A final size relation for epidemic models", Mathematical Biosciences and Engineering 4 (2007), 159–175, Theorems 2.1 and 5.1, <https://doi.org/10.3934/mbe.2007.4.159>.
