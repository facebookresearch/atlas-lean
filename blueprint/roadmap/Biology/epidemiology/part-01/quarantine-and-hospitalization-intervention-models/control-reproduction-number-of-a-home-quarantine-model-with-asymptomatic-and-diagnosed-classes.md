# Control reproduction number of a home-quarantine model with asymptomatic and diagnosed classes

**Model.** In a population divided into susceptible $S$, home-quarantined $Q$, exposed $E$ (not infectious), asymptomatic infectious $A$, symptomatic infectious $I$, diagnosed (isolated) $D$ and recovered $R$ individuals,

$$
\begin{aligned}
\dot S &= -\beta S (I + \theta A) - pS + \lambda Q, & \dot Q &= pS - \lambda Q,\\
\dot E &= \beta S (I + \theta A) - \sigma E, & \dot A &= \sigma(1 - \rho) E - (\epsilon_A + \gamma_A) A,\\
\dot I &= \sigma\rho E - (\gamma_I + d_I + \epsilon_I) I, & \dot D &= \epsilon_A A + \epsilon_I I - (d_D + \gamma_D) D,\\
\dot R &= \gamma_A A + \gamma_I I + \gamma_D D ,
\end{aligned}
$$

where $\beta > 0$ is the contact rate, $\theta \in (0,1)$ the relative infectiousness of asymptomatic cases, $p$ and $\lambda$ the quarantine and release rates, $\sigma$ the rate of leaving latency, $\rho \in [0,1]$ the symptomatic fraction, $\epsilon_A, \epsilon_I$ the diagnosis rates, $\gamma_A, \gamma_I, \gamma_D$ recovery rates and $d_I, d_D$ disease death rates. Diagnosed individuals are isolated and do not transmit.

**Proposition (control reproduction number).** At the infection-free state with susceptible level $S_0$, the next-generation matrices on the infected compartments $(E, A, I)$ are

$$
\mathcal{F} = \begin{pmatrix} 0 & \beta\theta S_0 & \beta S_0 \\ 0 & 0 & 0 \\ 0 & 0 & 0 \end{pmatrix}, \qquad \mathcal{V} = \begin{pmatrix} \sigma & 0 & 0 \\ -\sigma(1 - \rho) & \epsilon_A + \gamma_A & 0 \\ -\sigma\rho & 0 & \gamma_I + d_I + \epsilon_I \end{pmatrix},
$$

and the control reproduction number is

$$
\mathcal{R}_c^0 = \rho(\mathcal{F}\mathcal{V}^{-1}) = \Big(\frac{\beta\theta(1 - \rho)}{\epsilon_A + \gamma_A} + \frac{\beta\rho}{\gamma_I + d_I + \epsilon_I}\Big) S_0 .
$$

Replacing $S_0$ by $S(t)$ gives the effective control reproduction number $\mathcal{R}_c(t)$, which decreases as home quarantine moves susceptibles into $Q$ and as faster diagnosis shortens the infectious periods $1/(\epsilon_A + \gamma_A)$ and $1/(\gamma_I + d_I + \epsilon_I)$.

## Expansion

Since $\mathcal{F}$ has a single nonzero row, $\mathcal{F}\mathcal{V}^{-1}$ has rank one and its spectral radius is the $(1,1)$ entry: the expected number of new exposed individuals produced by one exposed individual. That individual becomes asymptomatic with probability $1 - \rho$ and then infects at rate $\beta\theta S_0$ for a mean time $1/(\epsilon_A + \gamma_A)$, or becomes symptomatic with probability $\rho$ and infects at rate $\beta S_0$ for a mean time $1/(\gamma_I + d_I + \epsilon_I)$. The quarantine flow $S \leftrightarrow Q$ enters only through the available susceptible level: at the quarantine equilibrium $S_0 = \lambda N/(p + \lambda)$ for a closed population of size $N$ without disease, so stronger quarantine (larger $p$, smaller $\lambda$) lowers $\mathcal{R}_c^0$ proportionally.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Sources

- Jiwei Jia, Jian Ding, Siyu Liu and Guidong Liao, "Modeling the Control of COVID-19: Impact of Policy Interventions and Meteorological Factors", arXiv (2020), Section 2 (model and control reproduction number), <https://doi.org/10.48550/arXiv.2003.02985>.
- P. van den Driessche and J. Watmough, "Reproduction numbers and sub-threshold endemic equilibria for compartmental models of disease transmission", Mathematical Biosciences 180 (2002), 29–48, <https://doi.org/10.1016/S0025-5564(02)00108-6>.
