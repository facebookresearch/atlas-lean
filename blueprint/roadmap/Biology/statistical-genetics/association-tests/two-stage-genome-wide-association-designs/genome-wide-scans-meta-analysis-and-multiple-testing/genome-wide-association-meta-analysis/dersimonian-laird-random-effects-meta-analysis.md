# DerSimonian–Laird random-effects association test

**Setting.** At one SNP $j$, studies $i = 1, \dots, N_j$ ($N_j \ge 2$) report effect estimates $y_i = \beta_{ij}$ with known sampling variances $v_i = V_{ij} > 0$, following the [random-effects model](../../../../../../Probability/not-yet-classified/part-17/der-simonian-laird/random-effects-model.md) $y_i = \beta_j + \delta_i + e_i$ with between-study variance $\Delta^2 = \tau_j^2$. Let $\hat\tau_j^2$ be the [DerSimonian–Laird estimator](../../../../../../Probability/not-yet-classified/part-17/der-simonian-laird/dl-estimator.md) of $\tau_j^2$ and $\hat\beta_j^\ast$ the [random-effects pooled estimate](../../../../../../Probability/not-yet-classified/part-17/der-simonian-laird/pooled-estimate.md) with $\Delta^2 = \hat\tau_j^2$, that is, the average of the $\beta_{ij}$ with the inverse-variance weights of $V_{ij} + \hat\tau_j^2$. Put $w_{ij}^\ast = (V_{ij} + \hat\tau_j^2)^{-1}$.

**Test.** The conventional random-effects association test of $\beta_j = 0$ refers

$$T_j^\ast = (\hat\beta_j^\ast)^2 \sum_i w_{ij}^\ast$$

to the $\chi^2_1$ law, treating $\operatorname{Var}(\hat\beta_j^\ast) \approx (\sum_i w_{ij}^\ast)^{-1}$ as known.

## Remarks

Adding $\hat\tau_j^2$ to every study's variance inflates the variance of the combined estimate, correcting the deflation that the fixed-effects variance shows under heterogeneity, and pulls the weights toward equality. The null hypothesis $\beta_j = 0$ is tested with this inflated variance even though heterogeneity of effects can arise only when there is an effect. When all $V_{ij}$ are equal, $\hat\beta_j^\ast$ is the unweighted mean (see [equal sampling variances](../../../../../../Probability/not-yet-classified/part-17/der-simonian-laird/equal-variances.md)) and its stated variance is at least the fixed-effects one, so $T_j^\ast$ never exceeds the fixed-effects statistic ([the likelihood-ratio view](fixed-effects-meta-analysis-as-a-likelihood-ratio-test.md)). With unequal variances no such ordering holds in general: for estimates $(1, -4)$ with variances $(1, 4)$ the fixed-effects statistic is $0$, while $Q = 5$, $\hat\tau^2 = 10$ and the random-effects numerator is $1/11 - 4/14 \ne 0$, so $T^\ast > 0$ has the smaller $p$-value. The [Han–Eskin likelihood-ratio statistic](han-eskin-random-effects-meta-analysis.md), which keeps $\tau^2 = 0$ under the null, avoids assuming heterogeneity under the null.

## Depends on

- [Random-effects model](../../../../../../Probability/not-yet-classified/part-17/der-simonian-laird/random-effects-model.md)
- [DerSimonian–Laird estimator](../../../../../../Probability/not-yet-classified/part-17/der-simonian-laird/dl-estimator.md)
- [Random-effects pooled estimate](../../../../../../Probability/not-yet-classified/part-17/der-simonian-laird/pooled-estimate.md)

## Sources

- R. Mägi and A. P. Morris, "GWAMA: software for genome-wide association meta-analysis", BMC Bioinformatics 11 (2010), 288, Implementation ("Random effects meta-analysis"), <https://doi.org/10.1186/1471-2105-11-288>, PMCID PMC2893603.
- R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Controlled Clinical Trials 7 (1986), 177–188, <https://doi.org/10.1016/0197-2456(86)90046-2>.
- B. Han and E. Eskin, "Random-effects model aimed at discovering associations in meta-analysis of genome-wide association studies", American Journal of Human Genetics 88 (2011), 586–598, Material and Methods ("RE Approach", "RE Assumes Heterogeneity under the Null Hypothesis"), <https://doi.org/10.1016/j.ajhg.2011.04.014>, PMCID PMC3146723.
