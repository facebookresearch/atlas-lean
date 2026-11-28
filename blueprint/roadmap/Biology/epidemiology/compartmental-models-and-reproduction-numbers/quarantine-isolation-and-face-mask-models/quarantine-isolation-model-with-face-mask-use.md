# Quarantine–isolation model with face-mask use

Partition a closed population $N(t)$ into non-quarantined and quarantined susceptibles
($S_u$, $S_q$), non-quarantined and quarantined exposed ($E_u$, $E_q$), symptomatic infectious
($I_u$), asymptomatic or mildly symptomatic infectious ($I_a$), hospitalized or isolated ($I_h$),
intensive-care ($I_{icu}$) and recovered ($R$) individuals. A fraction $c_M \in (0,1]$ of the public
wears face-masks of efficacy $\epsilon_M \in (0,1]$, and the force of infection is

$$\lambda = \frac{\beta(1-\epsilon_M c_M)\,(I_u + \eta_a I_a + \eta_h I_h)}
{N - \theta_q (E_q + I_h + I_{icu})},$$

where $\beta$ is the effective contact rate, $\eta_a, \eta_h \in (0,1)$ are relative
infectiousnesses and $\theta_q \in (0,1]$ is the efficacy of quarantine, isolation and intensive
care in removing individuals from mixing. With per-contact infection probability $p \in (0,1]$,
the fraction $q$ of traced contacts who are infected when quarantined, and the remaining
parameters nonnegative rates or probabilities, the model is

$$
\begin{aligned}
\dot S_u &= -[(1-p) + (1-q)p + qp]\lambda S_u + \psi_q S_q, \\
\dot S_q &= (1-p)\lambda S_u - (\theta_j\lambda + \psi_q) S_q, \\
\dot E_u &= (1-q)p\lambda S_u - (\sigma_u + \alpha_u) E_u, \\
\dot E_q &= qp\lambda S_u + \alpha_u E_u + \theta_j \lambda S_q - \sigma_q E_q, \\
\dot I_u &= f_1 \sigma_u E_u - (\gamma_u + \phi_u + \delta_u) I_u, \\
\dot I_h &= f_2\sigma_u E_u + r\sigma_q E_q + \phi_u I_u + \sigma_a I_a - (\gamma_h + \nu_h + \delta_h) I_h, \\
\dot I_a &= (1 - f_1 - f_2)\sigma_u E_u + (1-r)\sigma_q E_q - (\gamma_a + \sigma_a + \delta_a) I_a, \\
\dot I_{icu} &= \nu_h I_h - (\gamma_{icu} + \delta_{icu}) I_{icu}, \\
\dot R &= \gamma_u I_u + \gamma_h I_h + \gamma_a I_a + \gamma_{icu} I_{icu}.
\end{aligned}
$$

Contact tracing enters through $\alpha_u$ (traced exposed moved to quarantine) and $\sigma_a$
(detected asymptomatic cases moved to isolation); $\theta_j \in [0,1]$ is the residual
susceptibility of quarantined susceptibles and $\psi_q$ the rate at which they are released. The
model has a line of disease-free equilibria $(S_u(0), 0, \dots, 0)$.

## Expansion

A susceptible making an effective contact is quarantined with probability $(1-p)$ if not infected,
quarantined while infected with probability $qp$, or infected without being traced with probability
$(1-q)p$; these three outcomes partition the contact, which is why the outflow from $S_u$ is
$\lambda S_u$. Face masks act on both acquisition and onward transmission and are modelled by the
single factor $1 - \epsilon_M c_M$ multiplying $\beta$, while social distancing lowers $\beta$
itself. There is no birth, death from other causes or waning immunity, so the system is of
Kermack–McKendrick type and admits final-size relations.

## Sources

- C. N. Ngonghala, E. Iboi, S. Eikenberry, M. Scotch, C. R. MacIntyre, M. H. Bonds, A. B. Gumel,
  "Mathematical assessment of the impact of non-pharmaceutical interventions on curtailing the 2019
  novel Coronavirus", Mathematical Biosciences 325 (2020) 108364, Section 2, "Formulation of
  mathematical model", Eq. (2.1) and the force of infection,
  <https://doi.org/10.1016/j.mbs.2020.108364> (PMC7252217).
