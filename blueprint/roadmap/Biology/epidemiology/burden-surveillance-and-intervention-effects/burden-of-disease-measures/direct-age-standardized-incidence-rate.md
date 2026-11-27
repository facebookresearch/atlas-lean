# Direct age-standardized incidence rate

Partition a population into age groups $i = 1, \dots, k$. In group $i$ let $d_i$ be the number of
incident cases and $Y_i > 0$ the person-years at risk, so that the **age-specific incidence rate** is
$\hat\lambda_i = d_i / Y_i$. Let $w_1, \dots, w_k \ge 0$ with $\sum_i w_i = 1$ be the age distribution
of a fixed standard population (for example the world standard population). The **directly
age-standardized rate** is the [directly standardized rate](../../../population-dynamics/life-tables-and-direct-standardization/directly-standardized-rate-eq-crude-rate.md) of the
rates $\hat\lambda_i$ under the standard sizes $w_i$; since $\sum_i w_i = 1$ it is the weighted sum

$$\mathrm{ASR} \;=\; \sum_{i=1}^k w_i\, \hat\lambda_i \;=\; \sum_{i=1}^k w_i \frac{d_i}{Y_i},$$

usually reported per $10^5$ or $10^6$ person-years.

**Theorem.** If the $d_i$ are independent with $d_i \sim \mathrm{Poisson}(\lambda_i Y_i)$, then $\mathrm{ASR}$ is an
unbiased estimator of $\sum_i w_i \lambda_i$, the crude rate the standard population would have
under the study population's age-specific rates, and

$$\operatorname{Var}(\mathrm{ASR}) \;=\; \sum_{i=1}^k \frac{w_i^2\, \lambda_i}{Y_i},
\qquad \widehat{\operatorname{Var}}(\mathrm{ASR}) \;=\; \sum_{i=1}^k \frac{w_i^2\, d_i}{Y_i^2},$$

the second being an unbiased estimator of the first. Two populations with identical age-specific
rates have identical expected $\mathrm{ASR}$ whatever their age structures, and if
$\lambda_i \le \lambda'_i$ for every $i$ then $\mathbb{E}\,\mathrm{ASR} \le \mathbb{E}\,\mathrm{ASR}'$: this is the
property that makes the index comparable across regions and periods.

## Depends on

- [Directly standardized rate is the crude rate with the standard's sizes](../../../population-dynamics/life-tables-and-direct-standardization/directly-standardized-rate-eq-crude-rate.md)

## Proof sketch

Linearity of expectation gives unbiasedness and the comparison, and independence with
$\operatorname{Var}(d_i) = \lambda_i Y_i$ gives the variance; $\mathbb{E}[d_i] = \lambda_i Y_i$ makes the
plug-in variance unbiased.

## Remarks

The crude rate $\sum_i d_i / \sum_i Y_i$ is instead a weighted mean with the study
population's own weights $Y_i / \sum_j Y_j$, so it confounds rate differences with differences in
age structure: a population that is merely older can show a higher crude rate while every
age-specific rate is lower. A divergence between the trend in case counts and the trend in the
standardized rate is therefore informative, the usual signature of population growth and ageing
acting on roughly stable age-specific risk. The value of $\mathrm{ASR}$ depends on the standard
chosen, so only rates computed against the same standard are comparable. In the childhood cancer
registry study the age-specific rates for 0-4, 5-9, 10-14 (and 15-19) years were averaged with world
standard population weights to give rates per million person-years for ages 0-14 (and 0-19); burden
of disease studies report age-standardized incidence, prevalence and DALY rates per $10^5$ in the
same way.

## Sources

- E. Steliarova-Foucher, M. Colombet, L. A. G. Ries et al., "International incidence of childhood cancer, 2001-10: a population-based registry study", *The Lancet Oncology* 18 (2017), <https://doi.org/10.1016/S1470-2045(17)30186-9> (PMC5461370), "Statistical analysis" (age-specific rates as cases over person-years; standardized rates as the weighted average of three or four age-specific rates with world standard population weights).
- GBD 2017 Inflammatory Bowel Disease Collaborators. The global, regional, and national burden of inflammatory bowel disease in 195 countries and territories, 1990-2017. *The Lancet Gastroenterology and Hepatology* 5:17-30 (2020), Methods. DOI <https://doi.org/10.1016/S2468-1253(19)30333-4>. PMCID PMC7026709.
