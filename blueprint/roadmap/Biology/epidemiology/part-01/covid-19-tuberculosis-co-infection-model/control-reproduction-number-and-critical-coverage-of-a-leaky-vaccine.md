# Control reproduction number and critical coverage of a leaky vaccine

The COVID-19-only sub-model of a COVID-19/tuberculosis co-infection model has susceptible $S$, vaccinated $V$, exposed $E$, asymptomatic $I_a$, symptomatic $I_s$ and recovered $R$ individuals, $N = S + V + E + I_a + I_s + R$, and force of infection $\lambda_c = \beta_c(\eta I_a + I_s)/N$:

$$\begin{aligned}
S' &= \pi + \omega V + \kappa_c R - (\nu + \mu + \lambda_c) S, & V' &= \nu S - (1-\varepsilon)\lambda_c V - (\omega + \mu) V,\\
E' &= \lambda_c S + (1-\varepsilon)\lambda_c V - (\sigma_c + \mu) E, & I_a' &= \sigma_c (1-\psi) E - (\mu + \delta_c + \gamma_1) I_a,\\
I_s' &= \sigma_c \psi E - (\mu + \delta_c + \gamma_2) I_s, & R' &= \gamma_1 I_a + \gamma_2 I_s - (\mu + \kappa_c) R.
\end{aligned}$$

Vaccination at rate $\nu$ with waning rate $\omega$ gives a **leaky** vaccine of efficacy $0 < \varepsilon < 1$, with $\pi, \mu, \beta_c, \sigma_c > 0$, the other rates $\ge 0$ and $\psi \in [0,1]$; $\psi$ is the symptomatic fraction and $\eta$ the relative infectiousness of asymptomatics. Write $k_3 = \mu + \sigma_c$, $k_4 = 1 - \psi$, $k_5 = \mu + \delta_c + \gamma_1$, $k_6 = \mu + \delta_c + \gamma_2$.

**Theorem.** The COVID-free equilibrium is

$$S^* = \frac{\pi(\mu + \omega)}{\mu(\mu + \omega + \nu)}, \qquad V^* = \frac{\pi \nu}{\mu(\mu + \omega + \nu)}, \qquad E = I_a = I_s = R = 0,$$

and the control reproduction number is

$$R_C = \frac{\beta_c \sigma_c\,(\psi k_5 + \eta k_4 k_6)}{k_3 k_5 k_6}\cdot\frac{\mu + \omega + (1-\varepsilon)\nu}{\mu + \omega + \nu} = R_\triangle\,(1 - \varepsilon\vartheta),$$

where $R_\triangle = \beta_c\sigma_c(\psi k_5 + \eta k_4 k_6)/(k_3 k_5 k_6)$ is the basic reproduction number without vaccination and $\vartheta = V^*/N^* = \nu/(\mu + \omega + \nu)$ is the vaccinated proportion at the disease-free state. The disease-free equilibrium is locally asymptotically stable if $R_C < 1$ and unstable if $R_C > 1$. Hence, when $R_\triangle > 1$, elimination requires vaccine coverage above the critical proportion

$$\vartheta_c = \frac{1}{\varepsilon}\left(1 - \frac{1}{R_\triangle}\right),$$

which is achievable only if $\varepsilon \ge 1 - 1/R_\triangle$.

**Endemic equilibria.** The endemic force of infection $\lambda_c^{**}$ solves $m_2 \lambda^2 + m_1 \lambda + m_0 = 0$ with $m_2 > 0$ and $m_0 = k_3 k_5 k_6 (\mu + \omega + \nu)(1 - R_C)$. So there is a unique endemic equilibrium when $R_C > 1$, while for $R_C < 1$ two endemic equilibria exist when $m_1 < 0$ and the discriminant is positive: the leaky vaccine together with loss of immunity can produce a backward bifurcation, in which case $R_C < 1$ alone does not guarantee elimination. For the TB-only sub-model, with latent $L$ and active $A$ tuberculosis, $L' = \lambda_t S - (\sigma_t + \mu + \gamma_3)L$ and $A' = \sigma_t L - (\mu + \delta_t + \gamma_4)A$ (transmission rate $\beta_t$, progression rate $\sigma_t$, TB death rate $\delta_t$, treatment rates $\gamma_3, \gamma_4$), the analogous threshold is $R_T = \beta_t \sigma_t / \big((\sigma_t + \mu + \gamma_3)(\mu + \delta_t + \gamma_4)\big)$; the source prints $\mu + \delta_t + \gamma_3$ as the first factor, a misprint its own proof of Theorem 6 does not use.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)
- [Unstable mode of the infected subsystem exactly when $R_0 > 1$](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)

## Expansion

With infected compartments $(E, I_a, I_s)$, new infections enter only $E$ at rate $\beta_c (S^* + (1-\varepsilon)V^*)/N^* \cdot (\eta I_a + I_s)$, and $V$ is lower bidiagonal with diagonal $(k_3, k_5, k_6)$ and transfers $\sigma_c k_4$, $\sigma_c \psi$ from $E$. The next-generation matrix has rank one, so $R_C$ is the expected infectiousness of one exposed person, $\sigma_c/k_3 \cdot (\eta k_4/k_5 + \psi/k_6)$, times the effective susceptible fraction $(S^* + (1-\varepsilon)V^*)/N^* = 1 - \varepsilon\vartheta$. Local stability then follows from the van den Driessche–Watmough threshold theorem. Solving $R_C = R_\triangle(1 - \varepsilon\vartheta) < 1$ for $\vartheta$ gives $\vartheta_c$. Substituting the endemic steady states, expressed through $\lambda_c^{**}$, into the definition of the force of infection gives the quadratic, whose constant term changes sign exactly at $R_C = 1$.

## Sources

- M. M. Ojo, O. J. Peter, E. F. D. Goufo and K. S. Nisar, "A mathematical model for the co-dynamics of COVID-19 and tuberculosis", Mathematics and Computers in Simulation (2023), Eqs. (5), (7)–(9), (12)–(17), (21), Theorems 2–6, <https://doi.org/10.1016/j.matcom.2023.01.014>, PMCID PMC9850643.
