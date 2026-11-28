# SEPIA compartmental model

Consider a closed community with compartments of susceptible ($S$), exposed ($E$), presymptomatic
infectious ($P$), severely symptomatic infectious ($I$), asymptomatic or mildly symptomatic
infectious ($A$), hospitalized ($H$), home-quarantined ($Q$), recovered ($R$) and dead ($D$)
individuals. All rates are nonnegative constants, $\sigma \in [0,1]$ is the probability that a
presymptomatic individual develops severe symptoms, and $\zeta \in [0,1]$ is the fraction of
isolated symptomatic individuals who are quarantined at home rather than hospitalized. With the
frequency-dependent force of infection

$$\lambda = \frac{\beta_P P + \beta_I I + \beta_A A}{S + E + P + I + A + R},$$

the SEPIA model is

$$
\begin{aligned}
\dot S &= -\lambda S, &
\dot E &= \lambda S - \delta_E E, \\
\dot P &= \delta_E E - \delta_P P, &
\dot I &= \sigma \delta_P P - (\eta + \gamma_I + \alpha_I) I, \\
\dot A &= (1-\sigma)\delta_P P - \gamma_A A, &
\dot H &= (1-\zeta)\eta I - (\gamma_H + \alpha_H) H, \\
\dot Q &= \zeta \eta I - \gamma_Q Q, &
\dot R &= \gamma_I I + \gamma_A A + \gamma_H H + \gamma_Q Q, \\
\dot D &= \alpha_I I + \alpha_H H .
\end{aligned}
$$

Here $\delta_E$ is the rate of leaving latency, $\delta_P$ the rate of leaving the presymptomatic
stage, $\eta$ the isolation rate of symptomatic cases, $\gamma_X$ recovery rates and $\alpha_X$
disease-induced death rates. Isolated ($H$, $Q$) and dead individuals do not transmit and are
excluded from the mixing denominator.

The term $\gamma_Q Q$ in $\dot R$ corrects the source's Eq. 1, which prints
$\dot R = \gamma_I I + \gamma_A A + \gamma_H H$. The source's text says that home-quarantined
individuals leave $Q$ upon recovery at rate $\gamma_Q$ and that recovered individuals enter $R$
independently of their compartment of origin, so the outflow $\gamma_Q Q$ from $Q$ enters $R$ and
the right-hand sides sum to zero.

## Expansion

The model is an SEIR scheme whose infectious period is split in two stages. A presymptomatic stage
of mean length $1/\delta_P$ captures transmission before illness onset, which is why the serial
interval can be shorter than the incubation period. The infectious period then branches into a
severe track, which is removed from the community by isolation at rate $\eta$, and a mild track
($A$) that keeps transmitting until recovery. Summing all equations shows that the total population
$S+E+P+I+A+H+Q+R+D$ is conserved. In a fully susceptible single community, an individual entering
$P$ produces on average $\beta_P/\delta_P + \sigma\beta_I/(\eta+\gamma_I+\alpha_I) + (1-\sigma)\beta_A/\gamma_A$ new infections, the one-community version of the spatial
reproduction number.

## Sources

- M. Gatto, E. Bertuzzo, L. Mari, S. Miccoli, L. Carraro, R. Casagrandi, A. Rinaldo, "Spread and
  dynamics of the COVID-19 epidemic in Italy: Effects of emergency containment measures",
  Proceedings of the National Academy of Sciences 117 (2020) 10484-10491, Materials and Methods,
  "Epidemiological Model", Eq. 1 and the force of infection,
  <https://doi.org/10.1073/pnas.2004978117> (PMC7229754).
