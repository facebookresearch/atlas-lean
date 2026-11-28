# Unconfoundedness of policy effects under stochastic SIRD dynamics

Consider locations observed in periods $t = 1, \dots, \mathcal T$, a binary policy indicator $D$ adopted at period $t^*$, and the untreated potential state $F_t(0) = (S_t(0), I_t(0), R_t(0), \delta_t(0))$ of a location of population $N$ (susceptible, currently infected, cumulative recovered and cumulative dead counts), with cumulative cases $C_t(0)$. Assume the source's stochastic SIRD model for untreated potential outcomes (its Eqs. (A.1)–(A.7)): for $t = 2, \dots, \mathcal T$, with parameters $\beta, \lambda, \gamma$ common to all locations,

$$I_t(0) = I_{t-1}(0) + \beta\,\frac{I_{t-1}(0)}{N}\,S_{t-1}(0) + u^I_t - \Delta R_t(0) - \Delta\delta_t(0), \qquad R_t(0) = R_{t-1}(0) + \lambda I_{t-1}(0) + u^R_t, \qquad \delta_t(0) = \delta_{t-1}(0) + \gamma I_{t-1}(0) + u^\delta_t,$$

$N = S_t(0) + I_t(0) + R_t(0) + \delta_t(0)$ and $C_t(0) = N - S_t(0)$, where the shocks $u_t = (u^I_t, u^R_t, u^\delta_t)$ satisfy $E[u_t \mid F_{t-1}(0), \dots, F_1(0), D = d] = 0$ (A.6) and $u_t \perp\!\!\!\perp (D, F_{t-2}(0), \dots, F_1(0)) \mid F_{t-1}(0)$ (A.7). Assume overlap: $P(D = 1) > \epsilon$ and $p(F_{t^*-1}) := P(D = 1 \mid F_{t^*-1}) < 1 - \epsilon$ almost surely, for some $\epsilon > 0$. Then for every $t \ge t^*$:

1. $E[C_t(0) \mid F_{t^*-1}, D = 1] = E[C_t(0) \mid F_{t^*-1}, D = 0]$ (unconfoundedness given the pre-policy epidemic state);
2. the average effect on the treated, $\mathrm{ATT}^C_t = E[C_t(1) - C_t(0) \mid D = 1]$, is identified by

$$\mathrm{ATT}^C_t = E\bigl[\omega(D, F_{t^*-1})\bigl(C_t - m^C_{0,t}(F_{t^*-1})\bigr)\bigr],$$

where $m^C_{0,t}(f) = E[C_t \mid F_{t^*-1} = f, D = 0]$ and

$$\omega(D, F) = \frac{D}{E[D]} - \frac{\dfrac{p(F)}{1 - p(F)}(1 - D)}{E\Bigl[\dfrac{p(F)}{1 - p(F)}(1 - D)\Bigr]}.$$

## Expansion

The Markov property gives $E[h(F_t(0)) \mid F_{t-1}(0), \dots, F_{t-k}(0), D = d] = E[h(F_t(0)) \mid F_{t-1}(0), D = d]$, and independence of the shock from $D$ removes the dependence on $d$; iterating from $t^*$ forward yields statement 1 for the whole state, hence for cumulative cases. Statement 2 is the standard propensity-weighted regression-adjustment representation of the ATT under unconfoundedness and overlap. The point is that comparing locations with the same current epidemic state is valid, while comparing their changes is not (see the companion result).

## Sources

- B. Callaway and T. Li, "Policy evaluation during a pandemic", Journal of Econometrics 236 (2023) 105454, <https://doi.org/10.1016/j.jeconom.2023.03.009>, PMCID PMC10276647. Section 4.2: Assumption 1, Proposition 1 and Theorem 2 (Eqs. (9)–(10)); Appendix A.1, Eqs. (A.1)–(A.7) (the stochastic SIRD model for untreated potential outcomes); Appendix B, Lemmas 1–2.
