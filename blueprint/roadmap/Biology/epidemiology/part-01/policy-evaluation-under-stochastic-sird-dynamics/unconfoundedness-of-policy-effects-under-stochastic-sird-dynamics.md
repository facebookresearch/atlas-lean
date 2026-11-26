# Unconfoundedness of policy effects under stochastic SIRD dynamics

Consider locations observed in periods $t = 1, \dots, \mathcal T$, a binary policy indicator $D$ adopted at period $t^*$, and the untreated potential state $F_t(0)$ of a location (susceptible, infected, recovered and dead counts, together with cumulative cases $C_t(0)$). Assume the stochastic SIRD model for untreated potential outcomes: $F_t(0) = r(F_{t-1}(0), u_t)$ for a fixed transition map $r$, where the shock $u_t$ is independent of $D$ and of $F_{t-2}(0), F_{t-3}(0), \dots$ given $F_{t-1}(0)$. Assume overlap: $P(D = 1) > \epsilon$ and $p(F_{t^*-1}) := P(D = 1 \mid F_{t^*-1}) < 1 - \epsilon$ almost surely, for some $\epsilon > 0$. Then for every $t \ge t^*$:

1. $E[C_t(0) \mid F_{t^*-1}, D = 1] = E[C_t(0) \mid F_{t^*-1}, D = 0]$ (unconfoundedness given the pre-policy epidemic state);
2. the average effect on the treated, $\mathrm{ATT}^C_t = E[C_t(1) - C_t(0) \mid D = 1]$, is identified by

$$\mathrm{ATT}^C_t = E\bigl[\omega(D, F_{t^*-1})\bigl(C_t - m^C_{0,t}(F_{t^*-1})\bigr)\bigr],$$

where $m^C_{0,t}(f) = E[C_t \mid F_{t^*-1} = f, D = 0]$ and

$$\omega(D, F) = \frac{D}{E[D]} - \frac{\dfrac{p(F)}{1 - p(F)}(1 - D)}{E\Bigl[\dfrac{p(F)}{1 - p(F)}(1 - D)\Bigr]}.$$

## Expansion

The Markov property gives $E[h(F_t(0)) \mid F_{t-1}(0), \dots, F_{t-k}(0), D = d] = E[h(F_t(0)) \mid F_{t-1}(0), D = d]$, and independence of the shock from $D$ removes the dependence on $d$; iterating from $t^*$ forward yields statement 1 for the whole state, hence for cumulative cases. Statement 2 is the standard propensity-weighted regression-adjustment representation of the ATT under unconfoundedness and overlap. The point is that comparing locations with the same current epidemic state is valid, while comparing their changes is not (see the companion result).

## Sources

- B. Callaway and T. Li, "Policy evaluation during a pandemic", Journal of Econometrics 236 (2023) 105454, <https://doi.org/10.1016/j.jeconom.2023.03.009>, PMCID PMC10276647. Section 4.2: Assumption 1, Proposition 1 and Theorem 2 (Eqs. (9)–(10)); Appendix B, Lemmas 1–2.
