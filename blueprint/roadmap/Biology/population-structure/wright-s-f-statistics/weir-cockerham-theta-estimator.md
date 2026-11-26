# Weir–Cockerham estimator of $\theta$ (moment estimator of $F_{ST}$)

For one biallelic locus, suppose $n_i \ge 1$ diploid individuals are sampled from subpopulation $i = 1, \dots, r$ ($r \ge 2$), with total $\sum_i n_i$ and $\bar n = \sum_i n_i / r > 1$. Let $\tilde p_i$ be the sample frequency of allele $A$ and $\tilde h_i$ the observed proportion of individuals heterozygous for $A$ in sample $i$. Define

$$\bar p = \sum_i \frac{n_i \tilde p_i}{r \bar n}, \qquad s^2 = \sum_i \frac{n_i (\tilde p_i - \bar p)^2}{(r-1)\bar n}, \qquad \bar h = \sum_i \frac{n_i \tilde h_i}{r \bar n},$$

$$n_c = \frac{r \bar n - \sum_i n_i^2 / (r \bar n)}{r - 1}.$$

The Weir–Cockerham statistics are

$$a = \frac{\bar n}{n_c}\left\{ s^2 - \frac{1}{\bar n - 1}\left[ \bar p (1 - \bar p) - \frac{r-1}{r} s^2 - \frac{\bar h}{4} \right] \right\},$$

$$b = \frac{\bar n}{\bar n - 1}\left[ \bar p (1 - \bar p) - \frac{r-1}{r} s^2 - \frac{2 \bar n - 1}{4 \bar n} \bar h \right], \qquad c = \frac{\bar h}{2},$$

and the estimators are

$$\hat\theta = \frac{a}{a + b + c}, \qquad \hat F = 1 - \frac{c}{a + b + c}, \qquad \hat f = 1 - \frac{c}{b + c}.$$

Under the replicate-population model, $a$, $b$ and $c$ are unbiased for the [variance components](weir-cockerham-variance-components.md) $\sigma_a^2$, $\sigma_b^2$, $\sigma_c^2$; like those components (and $\sigma_b^2$ in particular), they can be negative. For several alleles or loci, the components are summed before the ratio is taken, $\hat\theta = \sum a / \sum (a + b + c)$ (a ratio of sums, not a mean of per-locus ratios).

## Depends on

- [Weir–Cockerham variance components of allele frequencies](weir-cockerham-variance-components.md)
- [Wright's hierarchical F-statistics identity](hierarchical-f-statistics.md)

## Proof depends on

None beyond the expected mean squares of the nested analysis of variance and linearity of expectation, as the Expansion describes.

## Expansion

The analysis-of-variance mean squares of the indicator data (between populations, between individuals within populations, within individuals) have expectations linear in $\sigma_a^2, \sigma_b^2, \sigma_c^2$; equating each mean square to its expectation and solving the resulting linear system gives the estimated components $a$, $b$, $c$, which are linear combinations of the mean squares rather than mean squares themselves. The constant $n_c$ is the usual unbalanced-ANOVA correction and equals $\bar n$ when all $n_i$ are equal. Because $\hat\theta$ is a ratio of unbiased estimators it is not itself unbiased, but it accounts for both the number of sampled populations and the sample sizes, which distinguishes it from plug-in estimates of $F_{ST}$; it can be negative when the between-population mean square is small.

## Sources

- B. S. Weir and C. C. Cockerham, *Estimating F-statistics for the analysis of population structure*, Evolution 38 (1984), 1358–1370. <https://doi.org/10.1111/j.1558-5646.1984.tb05657.x>
