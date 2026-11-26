# Weir–Cockerham variance components of allele frequencies

Consider one biallelic locus with allele $A$, sampled from $r$ subpopulations that are replicates of the same evolutionary process. Let $p$ be the expected frequency of $A$ over replicate populations. For a gene copy define the indicator $x = 1$ if it carries $A$ and $x = 0$ otherwise. Write

- $F$ for the correlation of $x$ between the two gene copies within an individual (total inbreeding),
- $\theta$ for the correlation of $x$ between gene copies in different individuals of the same subpopulation (coancestry),
- $f$ for the correlation within individuals relative to the subpopulation, so that $1 - F = (1 - f)(1 - \theta)$.

Then the total variance $p(1-p)$ of $x$ decomposes into three components, between subpopulations, between individuals within subpopulations, and between gene copies within individuals:

$$\sigma_a^2 = p(1-p)\,\theta, \qquad \sigma_b^2 = p(1-p)\,(F - \theta), \qquad \sigma_c^2 = p(1-p)\,(1 - F),$$

with $\sigma_a^2 + \sigma_b^2 + \sigma_c^2 = p(1-p)$. These are covariance components, not variances of independent effects, and need not be nonnegative: $\sigma_b^2 < 0$ whenever $F < \theta$. For example, in identical replicate populations made entirely of heterozygotes, with the two allele copies of an individual ordered independently, $p = \tfrac12$, $F = -1$ and $\theta = 0$, so $\sigma_b^2 = -\tfrac14$. When $p(1-p) > 0$,

$$\theta = \frac{\sigma_a^2}{\sigma_a^2 + \sigma_b^2 + \sigma_c^2}, \qquad F = 1 - \frac{\sigma_c^2}{\sigma_a^2 + \sigma_b^2 + \sigma_c^2}, \qquad f = 1 - \frac{\sigma_c^2}{\sigma_b^2 + \sigma_c^2}.$$

Here $\theta$ plays the role of Wright's $F_{ST}$, $F$ of $F_{IT}$ and $f$ of $F_{IS}$.

## Depends on

- [Wright's hierarchical F-statistics identity](hierarchical-f-statistics.md)

## Proof depends on

None beyond bilinearity of covariance, as the Expansion describes.

## Expansion

This is a nested (hierarchical) random-effects model for the indicator $x$: the covariance of two copies in the same individual is $p(1-p)F$, in different individuals of the same subpopulation $p(1-p)\theta$, and in different subpopulations $0$. Writing $x = p + \alpha_{\text{pop}} + \beta_{\text{ind}} + \gamma_{\text{copy}}$ with $\alpha_{\text{pop}} = \mathbb E[x \mid \text{pop}] - p$, $\beta_{\text{ind}} = \mathbb E[x \mid \text{ind}] - \mathbb E[x \mid \text{pop}]$ and $\gamma_{\text{copy}}$ the rest, the covariance of copies sharing only the subpopulation is $p(1-p)\theta$; copies sharing the individual add $p(1-p)(F - \theta)$, which is negative when copies within an individual are less alike than copies from different individuals of the subpopulation (excess heterozygosity); the remaining within-individual part is $p(1-p)(1 - F)$. The ratios follow by division.

## Sources

- B. S. Weir and C. C. Cockerham, *Estimating F-statistics for the analysis of population structure*, Evolution 38 (1984), 1358–1370. <https://doi.org/10.1111/j.1558-5646.1984.tb05657.x>
