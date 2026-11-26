# Basic reproduction number of the θ-SEIHRD model

**Model.** A population of constant size $N$ is split into susceptible $S$, exposed and infectious $E$, infectious undetected-to-be $I$, undetected infectious $I_u$, hospitalized (detected) cases that will recover $H_R$ or die $H_D$, detected recovered $R_d$, undetected recovered $R_u$ and dead $D$. Let $\theta \in [0,1]$ be the fraction of cases that are detected and $\omega \in [0, \theta]$ the fraction that die, and let $\beta_E, \beta_I, \beta_{I_u}, \beta_{H_R}, \beta_{H_D} \ge 0$ be transmission rates and $\gamma_E, \gamma_I, \gamma_{I_u}, \gamma_{H_R}, \gamma_{H_D} > 0$ exit rates. With constant parameters and no control ($m \equiv 1$) or migration, the model is

$$\begin{aligned}
S' &= -\frac{S}{N}\big(\beta_E E + \beta_I I + \beta_{I_u} I_u + \beta_{H_R} H_R + \beta_{H_D} H_D\big), \\
E' &= \frac{S}{N}\big(\beta_E E + \beta_I I + \beta_{I_u} I_u + \beta_{H_R} H_R + \beta_{H_D} H_D\big) - \gamma_E E, \\
I' &= \gamma_E E - \gamma_I I, \qquad I_u' = (1 - \theta)\gamma_I I - \gamma_{I_u} I_u, \\
H_R' &= (\theta - \omega)\gamma_I I - \gamma_{H_R} H_R, \qquad H_D' = \omega\gamma_I I - \gamma_{H_D} H_D, \\
R_d' &= \gamma_{H_R} H_R, \qquad R_u' = \gamma_{I_u} I_u, \qquad D' = \gamma_{H_D} H_D .
\end{aligned}$$

**Proposition.** At the disease-free state $S = N$, the next-generation matrix of the infected compartments $(E, I, I_u, H_R, H_D)$ has rank one and spectral radius

$$R_0 = \frac{\beta_E}{\gamma_E} + \frac{\beta_I}{\gamma_I} + \frac{(1 - \theta)\beta_{I_u}}{\gamma_{I_u}} + \frac{(\theta - \omega)\beta_{H_R}}{\gamma_{H_R}} + \frac{\omega\beta_{H_D}}{\gamma_{H_D}} .$$

With time-dependent control factors $m_X(t) \in [0,1]$ multiplying each $\beta_X$, the effective reproduction number is the same expression with $\beta_X$ replaced by $m_X(t)\beta_X$ and multiplied by $S(t)/N$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

New infections enter only $E$, so $F$ has a single nonzero row $(\beta_E, \beta_I, \beta_{I_u}, \beta_{H_R}, \beta_{H_D})$ and $R_0 = F V^{-1} e_E$, the expected total infectiousness of one newly infected person. The transition matrix $V$ is lower triangular: a new case spends mean time $1/\gamma_E$ in $E$, then surely $1/\gamma_I$ in $I$, then enters $I_u$, $H_R$ or $H_D$ with probabilities $1 - \theta$, $\theta - \omega$ and $\omega$ and stays a mean time $1/\gamma_X$ there. Summing $\beta_X$ times the expected residence time in $X$ gives the formula, which matches the nested fraction printed in the source after expansion. The detection fraction $\theta$ shifts weight between undetected and hospitalized infectiousness, so undetected cases raise $R_0$ when $\beta_{I_u}/\gamma_{I_u}$ exceeds the hospitalized terms.

## Sources

- B. Ivorra, M. R. Ferrández, M. Vela-Pérez and A. M. Ramos, *Mathematical modeling of the spread of the coronavirus disease 2019 (COVID-19) taking into account the undetected infections. The case of China*, Communications in Nonlinear Science and Numerical Simulation (2020). <https://doi.org/10.1016/j.cnsns.2020.105303> (PMCID: PMC7190554). Section 2, system (3) and "Outputs of the model".
- P. van den Driessche and J. Watmough, *Reproduction numbers and sub-threshold endemic equilibria for compartmental models of disease transmission*, Mathematical Biosciences (2002). <https://doi.org/10.1016/S0025-5564(02)00108-6>
