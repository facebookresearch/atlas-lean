# Recent infection and reinfection under partial protection

Work in the setting of the [cumulative hazard model](cumulative-hazard-model-of-infection-prevalence-by-age.md): hazard $\lambda(u) \ge 0$, cumulative hazard $H(s,t) = \int_s^t \lambda$, infection lifelong. Fix a look-back window $w > 0$ and a person of age $a \ge w$ at time $T$. Suppose that a previously infected person can be reinfected, with hazard reduced by a factor $1-\rho$, where $\rho \in [0,1]$ is the **protection against reinfection**.

**Proposition.**

1. The probability of a first infection within the last $w$ years is

$$P_{\mathrm{first}}(a,T) = e^{-H(T-a,\,T-w)}\Big(1 - e^{-H(T-w,\,T)}\Big).$$

2. The probability of being infected or reinfected within the last $w$ years is

$$P_{\mathrm{recent}}(a,T) = P_{\mathrm{first}}(a,T) + \Big(1 - e^{-H(T-a,\,T-w)}\Big)\Big(1 - e^{-(1-\rho)H(T-w,\,T)}\Big).$$

3. $P_{\mathrm{first}} \le P_{\mathrm{recent}} \le 1 - e^{-H(T-w,T)}$; the left equality holds when $\rho = 1$ and the right one when $\rho = 0$.
4. If after time $T$ there is no further transmission and infected people develop disease at a constant remote activation rate $\kappa$, the disease incidence produced by the latent pool at a later time is $\kappa$ times the prevalence of infection at that time.

## Depends on

- [Cumulative hazard model of infection prevalence by age](cumulative-hazard-model-of-infection-prevalence-by-age.md)

## Proof sketch

Split histories at time $T-w$. A first recent infection requires escaping infection on $[T-a, T-w]$ and then being infected on $[T-w, T]$; a recent reinfection requires prior infection and then an event of the reduced hazard $(1-\rho)\lambda$ on the window. The two events are disjoint, so their probabilities add. Part 3 follows from $0 \le 1-\rho \le 1$ and the identity $P_{\mathrm{first}} + (1-e^{-H(T-a,T-w)})(1-e^{-H(T-w,T)}) = 1 - e^{-H(T-w,T)}$. The latent tuberculosis re-estimation used $w = 2$ years and a beta-distributed protection with median 79% (sensitivity analysis 50%), finding that about 0.8% of the world population (about 55.5 million people) had been infected within two years. Part 4 with $\kappa = 0.15\%$ per year gives an incidence of $150 \times$ prevalence per 100,000 per year; the projected 2035 prevalence of about 11% then yields the reported 16.5 per 100,000 per year, above the End TB target of 10.

## Sources

- R. M. G. J. Houben and P. J. Dodd, "The global burden of latent tuberculosis infection: a re-estimation using mathematical modelling", PLoS Medicine 13 (2016) e1002152, Methods (recent infection, protection against reinfection, remote activation) and Results ("Recent Infection and Isoniazid Resistance", "Current Burden of LTBI and End TB Strategy Targets"), <https://doi.org/10.1371/journal.pmed.1002152>, PMCID PMC5079585.
