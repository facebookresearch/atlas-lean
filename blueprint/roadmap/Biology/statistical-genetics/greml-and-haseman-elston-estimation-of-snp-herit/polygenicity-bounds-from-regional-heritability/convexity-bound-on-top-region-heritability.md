# Convexity bound on heritability concentrated in top regions

Partition the genome into $M$ regions (for instance 1-Mb windows) and let $h^2_1, \dots, h^2_M \ge 0$ be the true heritabilities explained by the regions, with total $h^2_g = \sum_m h^2_m$. Suppose each region's heritability is estimated by a nonnegativity-constrained variance-component estimator, so that the estimate is exactly zero with positive probability, and let

$$P(x) = \Pr\big(\hat{h}^2_m = 0 \;\big|\; h^2_m = x\big)$$

be that probability as a function of the true value, a decreasing function of $x$ determined by the sample and the genotypes, not by the trait. Assume $P$ is convex and differentiable on $[0, \infty)$.

**Bound on the expected count.** Let $Z = \sum_m \mathbb{1}\{\hat{h}^2_m = 0\}$ be the number of zero estimates, so $\mathbb{E} Z = \sum_m P(h^2_m)$. Fix $k < M$ and suppose the $k$ largest regions carry total heritability $x = h^2_{\text{top}}$, so that $k h^2_g / M \le x \le h^2_g$. Then by convexity (Jensen's inequality applied separately to the top $k$ and the remaining $M - k$ regions),

$$\mathbb{E} Z \;\ge\; k \, P\!\left( \frac{x}{k} \right) + (M - k)\, P\!\left( \frac{h^2_g - x}{M - k} \right) \;=:\; \Phi_k(x).$$

Equality holds when heritability is spread evenly within each of the two groups; if $P$ is strictly convex, only then. On the feasible range, $\Phi_k'(x) = P'(x/k) - P'\big((h^2_g - x)/(M - k)\big) \ge 0$, because the mean of the top group is at least the mean of the rest and $P'$ is nondecreasing. So $\Phi_k$ is **nondecreasing**: concentrating a fixed total in the top $k$ regions raises the smallest expected number of zero estimates compatible with it.

**From the count to a bound.** The inequality constrains $\mathbb{E} Z$, not the observed count: under any concentration $x$ an observed $Z$ below $\Phi_k(x)$ is possible. The observed count $z$ estimates $\mathbb{E} Z$, and Loh et al. form a confidence bound from it: with $\widehat{\mathrm{se}}(z)$ the standard error of the count, every $x$ with $\Phi_k(x) > z + 1.96\,\widehat{\mathrm{se}}(z)$ is rejected, so the upper bound on $h^2_{\text{top}}$ is the largest $x$ with $\Phi_k(x) \le z + 1.96\,\widehat{\mathrm{se}}(z)$. Using $z$ itself in place of the confidence limit gives the point version of the same bound.

A matching lower bound needs no convexity: estimate regional heritabilities in part of the sample, rank the regions, and estimate the heritability of the top-ranked set in a held-out part; cross-validation then yields an unbiased estimate of the heritability explained by regions selected independently of the evaluation data.

## Proof depends on

- [Jensen's inequality](../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

The argument turns a nuisance of constrained estimation, the atom at zero, into a measurement. $P$ is a property of the estimator and the genotype data, obtainable by simulating traits of known architecture on the real genotypes, and it is empirically convex and well fitted by a sum of two decreasing exponentials. Given $P$, the expected count of zero estimates is a statistic of the whole architecture, and Jensen's inequality, for the uniform distribution on each group's per-region heritabilities, identifies the architecture minimizing that expectation at fixed $h^2_{\text{top}}$: an even split within each group. The bound uses no distributional assumption on effect sizes, only the convexity of $P$ and the additivity of the per-region expectations, and it is therefore robust to the number of causal variants and to the shape of the effect-size distribution, exactly the quantities that per-region estimates cannot resolve. Its statistical guarantee comes from the confidence limit on $\mathbb{E} Z$, not from the inequality.

## Sources

- P.-R. Loh, G. Bhatia, A. Gusev et al., "Contrasting genetic architectures of schizophrenia and other complex diseases using fast variance-components analysis", Nature Genetics 47 (2015), 1385–1392, Online Methods ("Bounding the SNP-heritability explained by top 1Mb regions") and Fig. 2, <https://doi.org/10.1038/ng.3431>, PMCID PMC4666835.
