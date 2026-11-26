# Effective reproduction ratio under time-varying contact and diagnosis rates

Consider a closed population split into susceptibles $S$, exposed $E$, symptomatic infectives $I$, asymptomatic infectives $A$, quarantined susceptibles $S_q$, quarantined exposed $E_q$, hospitalized (isolated) cases $H$ and recovered $R$, evolving by

$$\begin{aligned}
S' &= -\bigl(\beta c(t) + c(t) q (1-\beta)\bigr) S (I + \theta A) + \lambda S_q, \\
E' &= \beta c(t) (1-q) S (I + \theta A) - \sigma E, \\
I' &= \sigma \varrho E - \bigl(\delta_I(t) + \alpha + \gamma_I\bigr) I, \\
A' &= \sigma (1-\varrho) E - \gamma_A A, \\
S_q' &= (1-\beta) c(t) q S (I + \theta A) - \lambda S_q, \\
E_q' &= \beta c(t) q S (I + \theta A) - \delta_q E_q, \\
H' &= \delta_I(t) I + \delta_q E_q - (\alpha + \gamma_H) H, \\
R' &= \gamma_I I + \gamma_A A + \gamma_H H,
\end{aligned}$$

where $c(t)$ is the contact rate, $\beta \in [0,1]$ the transmission probability per contact, $q \in [0,1)$ the fraction of contacts traced and quarantined, $\theta \ge 0$ the relative infectiousness of asymptomatic cases, $\varrho \in [0,1]$ the probability that an exposed individual becomes symptomatic, $\sigma > 0$ the rate of leaving latency, $\delta_I(t) > 0$ the diagnosis (isolation) rate of symptomatic cases, $\alpha \ge 0$ the disease-induced death rate, $\gamma_I, \gamma_A > 0$ recovery rates, and $\lambda, \delta_q > 0$ the release and hospitalization rates from quarantine. Interventions are modelled by

$$c(t) = (c_0 - c_b) e^{-r_1 t} + c_b, \qquad \frac{1}{\delta_I(t)} = \Bigl(\frac{1}{\delta_{I0}} - \frac{1}{\delta_{If}}\Bigr) e^{-r_2 t} + \frac{1}{\delta_{If}},$$

with $c_b < c_0$ and $\delta_{If} > \delta_{I0}$, so contacts decay to a floor $c_b$ and the diagnosis delay shrinks to $1/\delta_{If}$. With $S_0$ the susceptible population at the disease-free state, the effective daily reproduction ratio is

$$R_d(t) = \left[\frac{\beta \varrho c(t) (1-q)}{\delta_I(t) + \alpha + \gamma_I} + \frac{\beta c(t) \theta (1-\varrho)(1-q)}{\gamma_A}\right] S_0 .$$

For each fixed $t$, $R_d(t)$ equals the spectral radius of the next-generation matrix of the transmitting subsystem $(E, I, A)$ with the coefficients $c$ and $\delta_I$ frozen at their time-$t$ values, so $R_d(t) < 1$ is the frozen-coefficient threshold for decline of new infections.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Quarantined exposed individuals $E_q$ move to $H$, which does not appear in the force of infection, so only $E$, $I$ and $A$ generate new transmitting infections. New transmitting infections enter only $E$, so the next-generation matrix has rank one and its spectral radius is the expected number of new $E$ produced by one $E$. That individual becomes symptomatic with probability $\varrho$ and then infects at rate $\beta c (1-q) S_0$ for a mean time $1/(\delta_I + \alpha + \gamma_I)$, or becomes asymptomatic with probability $1-\varrho$ and infects at the reduced rate $\theta \beta c (1-q) S_0$ for a mean time $1/\gamma_A$; summing the two branches gives $R_d$. Decreasing $c(t)$ scales both terms down, while increasing $\delta_I(t)$ shortens only the symptomatic infectious period, which is why the asymptomatic term bounds how far faster diagnosis alone can push $R_d$ below one. Because the coefficients vary in time, the frozen-coefficient threshold is a heuristic summary of a nonautonomous system rather than a stability theorem.

## Sources

- Tang B, Bragazzi NL, Li Q, Tang S, Xiao Y, Wu J. An updated estimation of the risk of transmission of the novel coronavirus (2019-nCov). *Infectious Disease Modelling* (2020), Methods, "Time-dependent dynamic model". DOI <https://doi.org/10.1016/j.idm.2020.02.001>. PMCID PMC7029158.
