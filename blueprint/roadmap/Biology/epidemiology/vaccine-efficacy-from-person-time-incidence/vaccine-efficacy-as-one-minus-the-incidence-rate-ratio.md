# Vaccine efficacy as one minus the incidence rate ratio

Consider a randomized trial with a vaccine arm ($v$) and a control arm ($p$). In arm $a \in \{v, p\}$
let $T_a > 0$ be the total surveillance time (person-time at risk) and suppose the number of
confirmed cases $X_a$ is Poisson with mean $\lambda_a T_a$, where $\lambda_a > 0$ is the incidence
rate, with $X_v$ and $X_p$ independent. The **vaccine efficacy** is

$$\mathrm{VE} \;=\; 1 - \frac{\lambda_v}{\lambda_p} \;=\; 1 - \mathrm{IRR},$$

the proportional reduction in incidence attributable to vaccination; $\mathrm{VE} \in (-\infty, 1)$,
with $\mathrm{VE} = 0$ for no effect and $\mathrm{VE} \to 1$ for complete protection. Its maximum
likelihood estimator is

$$\widehat{\mathrm{VE}} \;=\; 1 - \frac{X_v / T_v}{X_p / T_p},$$

defined when $X_p > 0$, because $X_a / T_a$ is the maximum likelihood estimator of $\lambda_a$ and
maximum likelihood estimators are invariant under reparametrization.

## Expansion

The rates are per unit of person-time rather than per participant, so unequal follow-up between
arms is absorbed into $T_v$ and $T_p$. In the BNT162b2 trial the primary end point had $X_v = 8$ cases
in $T_v = 2.214$ thousand person-years and $X_p = 162$ cases in $T_p = 2.222$ thousand person-years,
giving $\widehat{\mathrm{VE}} = 1 - (8/2.214)/(162/2.222) \approx 0.950$, the reported 95.0%.
Uncertainty about $\mathrm{VE}$ is most conveniently expressed after conditioning on
$X_v + X_p$, which reduces the two-Poisson model to a binomial one.

## Sources

- F. P. Polack, S. J. Thomas, N. Kitchin et al., "Safety and Efficacy of the BNT162b2 mRNA Covid-19 Vaccine", *New England Journal of Medicine* 383 (2020), <https://doi.org/10.1056/NEJMoa2034577> (PMC7745181), "Statistical Analysis" (vaccine efficacy estimated by $100 \times (1 - \mathrm{IRR})$ with rates per 1000 person-years) and Table 2.
