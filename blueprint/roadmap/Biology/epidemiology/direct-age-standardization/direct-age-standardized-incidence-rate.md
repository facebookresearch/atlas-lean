# Direct age-standardized incidence rate

Partition a population into age groups $i = 1, \dots, k$. In group $i$ let $d_i$ be the number of
incident cases and $Y_i > 0$ the person-years at risk, so that the **age-specific incidence rate** is
$\hat\lambda_i = d_i / Y_i$. Let $w_1, \dots, w_k \ge 0$ with $\sum_i w_i = 1$ be the age distribution
of a fixed standard population (for example the world standard population). The **directly
age-standardized rate** is

$$\mathrm{ASR} \;=\; \sum_{i=1}^k w_i\, \hat\lambda_i \;=\; \sum_{i=1}^k w_i \frac{d_i}{Y_i}.$$

If the $d_i$ are independent with $d_i \sim \mathrm{Poisson}(\lambda_i Y_i)$, then $\mathrm{ASR}$ is an
unbiased estimator of $\sum_i w_i \lambda_i$, the crude rate the standard population would have
under the study population's age-specific rates, and

$$\operatorname{Var}(\mathrm{ASR}) \;=\; \sum_{i=1}^k \frac{w_i^2\, \lambda_i}{Y_i},
\qquad \widehat{\operatorname{Var}}(\mathrm{ASR}) \;=\; \sum_{i=1}^k \frac{w_i^2\, d_i}{Y_i^2}.$$

Two populations with identical age-specific rates have identical expected $\mathrm{ASR}$ whatever
their age structures, which is the property that makes the index comparable across regions and
periods.

## Expansion

Linearity of expectation gives unbiasedness, and independence with
$\operatorname{Var}(d_i) = \lambda_i Y_i$ gives the variance; plugging in $\hat\lambda_i$ gives the
estimator. The crude rate $\sum_i d_i / \sum_i Y_i$ is instead a weighted mean with the study
population's own weights $Y_i / \sum_j Y_j$, so it confounds rate differences with differences in
age structure. In the childhood cancer registry study the age-specific rates for 0-4, 5-9, 10-14
(and 15-19) years were averaged with world standard population weights to give rates per million
person-years for ages 0-14 (and 0-19).

## Sources

- E. Steliarova-Foucher, M. Colombet, L. A. G. Ries et al., "International incidence of childhood cancer, 2001-10: a population-based registry study", *The Lancet Oncology* 18 (2017), <https://doi.org/10.1016/S1470-2045(17)30186-9> (PMC5461370), "Statistical analysis" (age-specific rates as cases over person-years; standardized rates as the weighted average of three or four age-specific rates with world standard population weights).
