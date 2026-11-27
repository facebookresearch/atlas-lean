# Logistic displacement of a variant and invariance under differential reporting

Let two variants have incidences $b_1(t) = a_1 e^{r_1 t}$ and $b_2(t) = a_2 e^{r_2 t}$ with $a_1, a_2 > 0$ and real growth rates $r_1, r_2$. The frequency of variant 2 among new infections is

$$p(t) = \frac{a_2 e^{r_2 t}}{a_1 e^{r_1 t} + a_2 e^{r_2 t}},$$

and its log-odds are linear in time:

$$\operatorname{logit} p(t) = \log\frac{a_2}{a_1} + (r_2 - r_1)\, t .$$

Hence $p$ is a logistic curve with slope $\Delta r = r_2 - r_1$; for $\Delta r > 0$, $p(t) \to 1$ as $t \to \infty$.

**Differential reporting.** Suppose each infection with variant $v$ is reported independently with a constant probability $x_v \in (0, 1]$, so that the expected reported incidence of variant $v$ is $x_v b_v(t)$. The share of variant 2 in the expected reported incidence is

$$q(t) = \frac{a_2 x_2 e^{r_2 t}}{a_1 x_1 e^{r_1 t} + a_2 x_2 e^{r_2 t}}, \qquad \operatorname{logit} q(t) = \log\frac{a_2 x_2}{a_1 x_1} + \Delta r\, t .$$

This is a ratio of expectations, not in general the expected value of the observed reported fraction: with one infection of each variant and reporting probabilities $1$ and $1/2$, the observed fraction of variant 2 has expectation $1/4$, while the share of expected reported incidence is $1/3$. Constant differential reporting shifts only the intercept of the logit of this share and leaves the slope $\Delta r$ unchanged. In particular, if $r_1 = r_2$, the reported share is constant in time whatever $x_1, x_2$ are, so a sustained rise in a variant's observed share cannot be produced by a time-invariant reporting bias alone.

## Proof sketch

Dividing numerator and denominator by $a_1 e^{r_1 t}$ gives $p = 1/(1 + (a_1/a_2) e^{-\Delta r\, t})$, from which the logit form is immediate; reporting multiplies each variant's incidence by a constant, i.e. multiplies $a_v$ by $x_v$. In practice $\Delta r$ is estimated by binomial or multinomial logistic regression of sequence counts (or of a proxy such as S-gene target failure, corrected for false positives) on sampling date, with region effects and overdispersion; the slope is the estimated growth advantage. Applied to UK sequence data for lineage B.1.1.7 this gave $\Delta r \approx 0.104$ per day relative to the previously dominant lineage.

## Depends on

- [Logistic growth curve](../../../population-dynamics/logistic-growth-equation/logistic.md)

## Proof depends on

- [Logit of the logistic curve](../../../population-dynamics/logistic-growth-equation/logit-logistic.md)

## Sources

- N. G. Davies, S. Abbott, R. C. Barnard, et al., "Estimated transmissibility and impact of SARS-CoV-2 lineage B.1.1.7 in England", Science 372 (2021) eabg3055, Materials and methods, "Competitive advantage and increased growth rate" and "Apparent growth of VOC 202012/01 not a result of testing artifacts", <https://doi.org/10.1126/science.abg3055> (PMC8128288).
