# Convexity bound on heritability concentrated in top regions

Partition the genome into $M$ regions (for instance 1-Mb windows) and let $h^2_1, \dots, h^2_M \ge 0$ be the true heritabilities explained by the regions, with total $h^2_g = \sum_m h^2_m$. Suppose each region's heritability is estimated by a nonnegativity-constrained variance-component estimator, so that the estimate is exactly zero with positive probability, and let

$$P(x) = \Pr\big(\hat{h}^2_m = 0 \;\big|\; h^2_m = x\big)$$

be that probability as a function of the true value, a decreasing function of $x$ determined by the sample and the genotypes, not by the trait. Assume $P$ is convex on $[0, \infty)$.

**Bound.** Let $Z = \sum_m \mathbb{1}\{\hat{h}^2_m = 0\}$ be the number of zero estimates, so $\mathbb{E} Z = \sum_m P(h^2_m)$. Fix $k < M$ and suppose the $k$ largest regions carry total heritability $h^2_{\text{top}}$. Then by convexity (Jensen's inequality applied separately to the top $k$ and the remaining $M - k$ regions),

$$\mathbb{E} Z \;\ge\; k \, P\!\left( \frac{h^2_{\text{top}}}{k} \right) + (M - k)\, P\!\left( \frac{h^2_g - h^2_{\text{top}}}{M - k} \right) \;=:\; \Phi_k\big(h^2_{\text{top}}\big),$$

with equality exactly when heritability is spread evenly within each of the two groups. Since $\Phi_k$ is decreasing in $h^2_{\text{top}}$ (concentrating heritability in few regions makes more regions estimate to zero), observing $Z = z$ excludes every concentration with $\Phi_k(h^2_{\text{top}}) > z$, which gives an upper bound on $h^2_{\text{top}}$: the largest $h^2_{\text{top}}$ with $\Phi_k(h^2_{\text{top}}) \le z$. Adding a multiple of the standard error of $z$ makes the bound conservative at a chosen confidence level.

A matching lower bound needs no convexity: estimate regional heritabilities in part of the sample, rank the regions, and estimate the heritability of the top-ranked set in a held-out part; cross-validation then yields an unbiased estimate of the heritability explained by regions selected independently of the evaluation data.

## Expansion

The argument turns a nuisance of constrained estimation — the atom at zero — into a measurement. $P$ is a property of the estimator and the genotype data, obtainable by simulating traits of known architecture on the real genotypes, and it is empirically convex and well fitted by a sum of two decreasing exponentials. Given $P$, the count of zero estimates is a statistic of the whole architecture, and the only thing Jensen's inequality is needed for is to identify the architecture minimizing the expected count at fixed $h^2_{\text{top}}$: an even split within each group. Because the bound is on the minimum, an observed count below that minimum is impossible under the hypothesized concentration, which is the exclusion. The bound uses no distributional assumption on effect sizes, only the convexity of $P$ and the additivity of the per-region expectations, and it is therefore robust to the number of causal variants and to the shape of the effect-size distribution — exactly the quantities that per-region estimates cannot resolve.

## Sources

- P.-R. Loh, G. Bhatia, A. Gusev et al., "Contrasting genetic architectures of schizophrenia and other complex diseases using fast variance-components analysis", Nature Genetics 47 (2015), 1385–1392, Online Methods ("Bounding the SNP-heritability explained by top 1Mb regions") and Fig. 2, <https://doi.org/10.1038/ng.3431>, PMCID PMC4666835.
