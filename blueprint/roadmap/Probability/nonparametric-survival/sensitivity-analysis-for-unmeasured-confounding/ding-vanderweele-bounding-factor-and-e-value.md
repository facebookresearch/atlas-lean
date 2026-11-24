# Bounding factor and E-value for unmeasured confounding (Ding–VanderWeele)

Let a binary exposure $E$ and a binary outcome $D$ be studied within one stratum of measured covariates, and let $U$ be an unmeasured confounder. Write $\mathrm{RR}_{\mathrm{obs}} \ge 1$ for the observed exposure–outcome risk ratio, $\mathrm{RR}_{\mathrm{true}}$ for the risk ratio standardized over $U$, $\mathrm{RR}_{EU}$ for the maximal ratio across levels of $U$ of the probability of that level among the exposed to that among the unexposed, and $\mathrm{RR}_{UD}$ for the maximal ratio of outcome risks across levels of $U$ within exposure groups. Ding and VanderWeele (2016) prove, without further assumptions on $U$, the sharp inequality

$$\frac{\mathrm{RR}_{\mathrm{obs}}}{\mathrm{RR}_{\mathrm{true}}} \le \mathrm{BF}(\mathrm{RR}_{EU}, \mathrm{RR}_{UD}) = \frac{\mathrm{RR}_{EU}\,\mathrm{RR}_{UD}}{\mathrm{RR}_{EU} + \mathrm{RR}_{UD} - 1},$$

so a confounder can explain away the observed risk ratio (bring $\mathrm{RR}_{\mathrm{true}}$ to $1$) only if $\mathrm{BF} \ge \mathrm{RR}_{\mathrm{obs}}$. This implies the Cornfield conditions that both $\mathrm{RR}_{EU}$ and $\mathrm{RR}_{UD}$ exceed $\mathrm{RR}_{\mathrm{obs}}$, and the stronger "high threshold" condition that the larger of the two be at least the common value $e$ at which $\mathrm{BF}(e, e) = \mathrm{RR}_{\mathrm{obs}}$; for example, for $\mathrm{RR}_{\mathrm{obs}} = 3$ the high threshold is $5.45$, and a confounder with $\mathrm{RR}_{EU} = 5.5$ and $\mathrm{RR}_{UD} = 3.1$ has $\mathrm{BF} = 2.24 < 3$ and so cannot explain the effect away. Solving $e^2/(2e - 1) = \mathrm{RR}$ gives $e = \mathrm{RR} + \sqrt{\mathrm{RR}(\mathrm{RR} - 1)}$, the E-value. Since $\mathrm{BF}$ is increasing in each argument and $\mathrm{BF}(x, y) < \min(x, y)$ for $x, y > 1$, having both ratios at least the E-value is sufficient for the bound to permit explaining away but not necessary: observed risks $68/125$ and $36/125$ ($\mathrm{RR}_{\mathrm{obs}} = 17/9$) are explained away by a confounder with $\mathrm{RR}_{EU} = 3$ and $\mathrm{RR}_{UD} = 5$, although the E-value is $(17 + \sqrt{136})/9 \approx 3.18 > 3$.

## Proof depends on

- [Finite-population average treatment effect](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/ate.md)

## Expansion

1. The model: the stratum, a categorical confounder with levels $0, \dots, K - 1$, its conditional laws given $E$, the risk kernels, the standardized risk ratio and the two maximal ratios.
2. The bounding-factor inequality, by a two-step maximization over the distribution of $U$ and over the risks, and its sharpness at the level of the risk kernels.
3. Properties of $\mathrm{BF}$: monotonicity, $\mathrm{BF}(x, y) < \min(x, y)$, the E-value as the solution of $\mathrm{BF}(e, e) = \mathrm{RR}$, the Cornfield and high-threshold conditions, and the explicit counterexample to the reading that both ratios must reach the E-value.
4. The causal reading: identification of the risk ratio, as a ratio of [average treatment effect](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/ate.md) means, by standardization under consistency and [strong ignorability](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/comp.md) given $U$ with positivity; under strict overlap the bound is a supremum, not attained when $\mathrm{RR}_{EU}, \mathrm{RR}_{UD} > 1$.

## Sources

- P. Ding and T. J. VanderWeele, Sensitivity analysis without assumptions, Epidemiology 27 (2016), 368–377, Result 1 and the high-threshold discussion. <https://doi.org/10.1097/ede.0000000000000457>
- Original result: T. J. VanderWeele and P. Ding, Sensitivity analysis in observational research: introducing the E-value, Ann. Intern. Med. 167 (2017), 268–274. <https://doi.org/10.7326/m16-2607> The threshold common to both confounding ratios follows Ding and VanderWeele (2016).
