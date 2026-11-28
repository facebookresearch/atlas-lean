# Attributable fractions for susceptibility and infectivity cofactors

**Setting.** At a fixed time, index the sexual acts between an uninfected and an infected partner by types $\tau$ occurring at rates $n_\tau \ge 0$. A type has baseline per-act transmission probability $\beta_\tau > 0$, a susceptibility cofactor $a_\tau \ge 1$ (for example the per-exposure enhancement of acquisition while the uninfected partner sheds herpes simplex virus 2) and an infectivity cofactor $c_\tau \ge 1$ (the enhancement of transmission while the infected partner is dually infected and shedding). In the rare-event regime the incidence is $\Lambda = \sum_\tau n_\tau\, \beta_\tau\, a_\tau\, c_\tau$. Write $\Lambda_{\neg a}$, $\Lambda_{\neg c}$, $\Lambda_{\neg ac}$ for the counterfactual incidences with all $a_\tau = 1$, all $c_\tau = 1$, or both, holding the population state fixed, and define the population attributable fractions

$$\mathrm{PAF}_{\mathrm{Sus}} = 1 - \frac{\Lambda_{\neg a}}{\Lambda}, \qquad \mathrm{PAF}_{\mathrm{Inf}} = 1 - \frac{\Lambda_{\neg c}}{\Lambda}, \qquad \mathrm{PAF}_{\mathrm{Sus+Inf}} = 1 - \frac{\Lambda_{\neg ac}}{\Lambda}.$$

**Proposition.**

1. $\max(\mathrm{PAF}_{\mathrm{Sus}}, \mathrm{PAF}_{\mathrm{Inf}}) \le \mathrm{PAF}_{\mathrm{Sus+Inf}} \le \mathrm{PAF}_{\mathrm{Sus}} + \mathrm{PAF}_{\mathrm{Inf}}$.
2. The gap in the upper bound is

$$\mathrm{PAF}_{\mathrm{Sus}} + \mathrm{PAF}_{\mathrm{Inf}} - \mathrm{PAF}_{\mathrm{Sus+Inf}} = \frac{1}{\Lambda}\sum_\tau n_\tau\, \beta_\tau\, (a_\tau - 1)(c_\tau - 1) \ge 0,$$

the share of incidence from acts in which both cofactors operate; equality holds if and only if no act type has both $a_\tau > 1$ and $c_\tau > 1$.
3. (Time-averaged relative risk) If the susceptibility cofactor $a > 1$ applies during a fraction $f$ of acts of an otherwise homogeneous group, the average per-act relative risk is $1 + f(a - 1)$, smaller than the per-exposure cofactor $a$.
4. These fractions count only direct effects at the given time; infections caused by the cofactor go on to cause further infections regardless of it, which is measured instead by the excess prevalence: prevalence with the interaction minus prevalence in the counterfactual without it.

## Expansion

Because $a_\tau, c_\tau \ge 1$, each counterfactual removes non-negative terms, giving $\Lambda_{\neg ac} \le \min(\Lambda_{\neg a}, \Lambda_{\neg c})$ and the left inequality of (1). For (2), $\Lambda - \Lambda_{\neg a} - \Lambda_{\neg c} + \Lambda_{\neg ac} = \sum n\beta(ac - c - a + 1) = \sum n\beta(a - 1)(c - 1)$. (3): with rates proportional to $f a + (1 - f)$ against $1$. In the source, a 32-compartment model of HIV and herpes simplex virus 2 coinfection calibrated to Kisumu, Kenya (per-exposure acquisition cofactor $4$, or $9$ in an alternative scenario, during primary infection and reactivation; infectivity cofactor $3$) attributed more than a quarter of incident HIV infections directly to herpes, with the infectivity channel slightly larger than the susceptibility channel because dually infected people reactivate more often; it reports $\mathrm{PAF}_{\mathrm{Sus+Inf}} \le \mathrm{PAF}_{\mathrm{Sus}} + \mathrm{PAF}_{\mathrm{Inf}}$ for exactly the double-counting reason in (2).

## Sources

- L. J. Abu-Raddad, A. S. Magaret, C. Celum, A. Wald, I. M. Longini, S. G. Self, L. Corey, "Genital herpes has played a more important role than any other sexually transmitted infection in driving HIV prevalence in Africa", PLoS ONE 3 (2008) e2230, Methods, "Measures of epidemiologic synergy" (definitions of $\mathrm{PAF}_{\mathrm{Sus}}$, $\mathrm{PAF}_{\mathrm{Inf}}$, $\mathrm{PAF}_{\mathrm{Sus+Inf}}$ and excess prevalence), <https://doi.org/10.1371/journal.pone.0002230> (PMC2377333).
