# mBAT-combo: Cauchy combination of set-based p-values

Let $P_1$ and $P_2$ be the p-values of the [fastBAT and mBAT tests](mbat-and-fastbat-set-based-tests.md) for the same gene region. The
**mBAT-combo** statistic is the equal-weight aggregated Cauchy combination

$$T = \frac12 \sum_{i=1}^2 \tan\{(0.5 - P_i)\pi\}, \qquad P_{\text{combo}} = \frac12 - \frac{\arctan T}{\pi}.$$

If $P_i$ is uniform on $(0,1)$, then $\tan\{(0.5 - P_i)\pi\}$ is standard Cauchy. Because a weighted average (weights summing to one)
of standard Cauchy variables is again standard Cauchy when they are independent, and remains approximately standard Cauchy in the
upper tail under arbitrary dependence of the underlying Gaussian test statistics (Liu and Xie 2020), $P_{\text{combo}}$ is an approximately
valid p-value at small significance levels without modelling the correlation between $P_1$ and $P_2$, and satisfies $P_{\text{combo}}/(2\min(P_1,P_2)) \to 1$ as $\min(P_1,P_2) \to 0$ with the other $p$-value fixed in $(0,1)$; when both are small, $P_{\text{combo}} \approx 2/(1/P_1 + 1/P_2)$.
For numerical stability, when $P_1 < 10^{-16}$ one uses $\tan\{(0.5 - P_1)\pi\} \approx 1/(P_1 \pi)$.

## Depends on

- [Quadratic-form set tests from GWAS summary statistics: fastBAT and mBAT](mbat-and-fastbat-set-based-tests.md)

## Expansion

The Cauchy transform maps $(0,1)$ onto $\mathbb{R}$ monotonically decreasingly, so small p-values map to large positive values with
tail $\Pr(C > t) \sim 1/(\pi t)$. In the extreme tail the sum is dominated by its largest term (when the other term stays bounded), which is why the combination keeps the
power of whichever of fastBAT or mBAT is better suited to the region's LD and effect pattern. (Li et al. 2023, combination formula
and its small-p approximation.)

## Sources

- A. Li, S. Liu, A. Bakshi et al., "mBAT-combo: A more powerful test to detect gene-trait associations from GWAS data", The American Journal of Human Genetics (2023), <https://doi.org/10.1016/j.ajhg.2022.12.006> (PMC9892780).
- Y. Liu and J. Xie, "Cauchy combination test: a powerful test with analytic p-value calculation under arbitrary dependency structures", Journal of the American Statistical Association 115 (2020), 393–402, <https://doi.org/10.1080/01621459.2018.1554485>.
