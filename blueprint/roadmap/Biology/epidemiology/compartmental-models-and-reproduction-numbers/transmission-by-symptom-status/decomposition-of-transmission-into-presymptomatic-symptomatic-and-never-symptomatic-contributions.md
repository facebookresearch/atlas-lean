# Decomposition of transmission into presymptomatic, symptomatic and never-symptomatic contributions

**Setting.** A fraction $p_{ns} \in [0, 1]$ of infections never become symptomatic and these transmit with relative infectiousness $r_{ns} \ge 0$ compared with infections that become symptomatic. For symptomatic infections, let $F$ be the distribution function of the incubation period (time from infection to symptom onset) and $I$ a probability density on $[0, \infty)$ describing infectiousness by time since infection, with incubation period and infectiousness profile independent. Define the fractions of all transmission due to never-symptomatic infections ($T_{ns}$), to symptomatic infections after onset ($T_s$) and before onset ($T_{ps}$):

$$T_{ns} = \frac{p_{ns}\, r_{ns}}{p_{ns}\, r_{ns} + 1 - p_{ns}}, \qquad T_s = (1 - T_{ns})\int_0^\infty F(\tau)\, I(\tau)\, d\tau, \qquad T_{ps} = (1 - T_{ns})\int_0^\infty \bigl(1 - F(\tau)\bigr)\, I(\tau)\, d\tau .$$

**Proposition.**

1. $T_{ns} + T_s + T_{ps} = 1$, with each term in $[0, 1]$.
2. $T_{ns}$ is increasing in $p_{ns}$ and in $r_{ns}$; with $p_{ns} = 0.3$ and $r_{ns} = 0.75$, $T_{ns} \approx 0.24$.
3. If the infectiousness profile is shifted later (replaced by a density $\tilde I$ that first-order stochastically dominates $I$), then $T_s$ does not decrease and $T_{ps}$ does not increase.
4. (Isolation ceiling) Immediate isolation at onset of every symptomatic case, with no other measure, prevents at most the fraction $T_s$ of transmission; at least $T_{ns} + T_{ps}$ remains.

## Expansion

(1): $\int F I + \int (1 - F) I = \int I = 1$. (2): $T_{ns} = x/(x + 1 - p_{ns})$ with $x = p_{ns} r_{ns}$; at the baseline, $0.225/0.925 \approx 0.243$. (3): $F$ is non-decreasing, and $\int F\,\tilde I \ge \int F\, I$ is the defining property of first-order stochastic dominance. (4): transmission after onset is the only part symptom-triggered isolation can reach. The source used a log-normal incubation period (median $5$ days, $95\%$ by day $12$) and a gamma infectiousness profile concentrated within $10$ days with peak at day $5$; at baseline, presymptomatic transmission was about $35\%$ and never-symptomatic $24\%$, so about $59\%$ of transmission came from people without symptoms; moving the peak to day $4$ or day $6$ changed this to $67\%$ or $51\%$, and most scenarios over peaks from $3$ to $7$ days and $T_{ns}$ from $0$ to $70\%$ kept it at or above one half. This decomposition motivated mask wearing, distancing and testing of people without symptoms.

## Sources

- M. A. Johansson, T. M. Quandelacy, S. Kada, P. V. Prasad, M. Steele, J. T. Brooks, et al., "SARS-CoV-2 transmission from people without COVID-19 symptoms", JAMA Network Open 4 (2021) e2035057, Methods (model equations for $T_{ns}$, $T_s$, $T_{ps}$) and Results, <https://doi.org/10.1001/jamanetworkopen.2020.35057> (PMC7791354).
