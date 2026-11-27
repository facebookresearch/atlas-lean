# Failure of parallel trends for cumulative epidemic cases

In the setting of [unconfoundedness under stochastic SIRD dynamics](unconfoundedness-of-policy-effects-under-stochastic-sird-dynamics.md), write $\Delta_{(t^*-1, t)}X_t = X_t - X_{t^*-1}$. For each $d \in \{0, 1\}$,

$$E\bigl[\Delta_{(t^*-1,t)}C_t(0) \mid D = d\bigr] = \sum_{s = t^*}^{t} E\Bigl[E\bigl[\Delta C_s(0) \mid F_{t^*-1}, D = d\bigr] \Bigm| D = d\Bigr].$$

Consequently the parallel-trends assumption $E[\Delta C_t(0) \mid D = 1] = E[\Delta C_t(0) \mid D = 0]$ does not hold in general, and the difference-in-differences estimand has bias

$$\sum_{s=t^*}^{t}\Bigl\{E\bigl[E[\Delta C_s(0) \mid F_{t^*-1}, D = 1] \bigm| D = 1\bigr] - E\bigl[E[\Delta C_s(0) \mid F_{t^*-1}, D = 0] \bigm| D = 0\bigr]\Bigr\}$$

relative to $\mathrm{ATT}^C_t$. The bias is zero when the distribution of the pre-policy epidemic state $F_{t^*-1}$ is the same in treated and untreated locations (or new cases do not depend on it), and non-zero in general otherwise.

## Depends on

- [Unconfoundedness of policy effects under stochastic SIRD dynamics](unconfoundedness-of-policy-effects-under-stochastic-sird-dynamics.md)

## Expansion

Telescoping the change in cumulative cases and conditioning each increment on $F_{t^*-1}$ gives the first identity. In an SIRD model new cases are a nonlinear function of current susceptibles and infecteds, not a location fixed effect plus a common time trend; locations that adopt a policy typically do so because they have more current cases, so their untreated case growth differs systematically. Difference-in-differences can therefore be severely biased, while conditioning on the pre-policy state is valid.

## Sources

- B. Callaway and T. Li, "Policy evaluation during a pandemic", Journal of Econometrics 236 (2023) 105454, <https://doi.org/10.1016/j.jeconom.2023.03.009>, PMCID PMC10276647. Section 4.1, Theorem 1.
