# Reproduction number with vertical transmission and leaky vaccination

**Model.** Population fractions $S, V, E, I, L, R$ (susceptible, vaccinated, exposed, severe infectious, mild infectious, recovered) with equal birth and death rate $\mu$ evolve as

$$\begin{aligned}
\dot S &= \mu - \rho\mu E - \beta S(I + L) + \lambda V - (\varepsilon + \mu)S, &
\dot V &= \varepsilon S + \varepsilon_1 E - \lambda V - \kappa\beta V(I + L) - \mu V,\\
\dot E &= \beta S(I + L) + \kappa\beta V(I + L) + \rho\mu E - (\alpha + \varepsilon_1 + \mu)E, &
\dot I &= \alpha\gamma E - (\delta_1 + \mu) I,\\
\dot L &= \alpha(1 - \gamma) E - (\delta_2 + \mu) L, &
\dot R &= \delta_1 I + \delta_2 L - \mu R,
\end{aligned}$$

where a fraction $\rho \in [0,1]$ of the offspring of exposed parents is born exposed (vertical transmission), $\varepsilon$ and $\varepsilon_1$ are vaccination rates of susceptible and exposed individuals, $\lambda$ is waning of vaccine protection, $\kappa \in [0,1]$ is the relative susceptibility of vaccinated individuals (leaky vaccine), $\alpha$ the progression rate, $\gamma$ the severe fraction and $\delta_1, \delta_2$ recovery rates. The disease-free equilibrium is $S_0 = (\lambda + \mu)/(\varepsilon + \lambda + \mu)$, $V_0 = \varepsilon/(\varepsilon + \lambda + \mu)$.

**Proposition.** With infected classes $(E, I, L)$ and new infections $F$ comprising both horizontal transmission and vertical births into $E$,

$$R_0 = \underbrace{\frac{\rho\mu}{\alpha + \varepsilon_1 + \mu}}_{R_E} + \underbrace{\frac{\beta\alpha\gamma(\lambda + \mu + \kappa\varepsilon)}{(\alpha + \varepsilon_1 + \mu)(\varepsilon + \lambda + \mu)(\delta_1 + \mu)}}_{R_I} + \underbrace{\frac{\beta\alpha(1 - \gamma)(\lambda + \mu + \kappa\varepsilon)}{(\alpha + \varepsilon_1 + \mu)(\varepsilon + \lambda + \mu)(\delta_2 + \mu)}}_{R_L},$$

the expected infections produced by one exposed individual through its exposed offspring, and through the severe and mild infectious stages it may pass through. The disease-free equilibrium is locally asymptotically stable for $R_0 < 1$ and unstable for $R_0 > 1$, globally asymptotically stable in the simplex for $R_0 \le 1$, and for $R_0 > 1$ a unique endemic equilibrium exists (globally stable when $\rho = \varepsilon_1 = 0$).

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

All new infections, horizontal or vertical, enter $E$, so only the $E$-row of $F$ is nonzero: $F_{EE} = \rho\mu$ and $F_{EI} = F_{EL} = \beta(S_0 + \kappa V_0) = \beta(\lambda + \mu + \kappa\varepsilon)/(\varepsilon + \lambda + \mu)$. Then $FV^{-1}$ has rank one and $R_0$ is its $(E,E)$ entry. With $V$ lower triangular, an exposed individual spends mean time $1/(\alpha + \varepsilon_1 + \mu)$ in $E$, producing $\rho\mu$ exposed newborns per unit time, and moves to $I$ or $L$ with probabilities $\alpha\gamma/(\alpha + \varepsilon_1 + \mu)$ and $\alpha(1-\gamma)/(\alpha + \varepsilon_1 + \mu)$, staying $1/(\delta_1 + \mu)$ or $1/(\delta_2 + \mu)$ while infecting at rate $\beta(S_0 + \kappa V_0)$. Vaccination lowers $R_0$ through the effective susceptible pool $S_0 + \kappa V_0$, which decreases in $\varepsilon$ when $\kappa < 1$; vertical transmission alone can sustain infection only if $R_E \ge 1$, i.e. $\rho\mu \ge \alpha + \varepsilon_1 + \mu$, which is impossible for $\rho \le 1$, so horizontal transmission is always required.

## Sources

- Y. Li, X. Liu and L. Wang, "Modelling the transmission dynamics and control of mumps in mainland China", International Journal of Environmental Research and Public Health 15 (2018), 33, Sections 2–3 (Eqs. (1)–(4), Proposition 1, Theorems 1–3), <https://doi.org/10.3390/ijerph15010033>, PMCID: PMC5800133.
