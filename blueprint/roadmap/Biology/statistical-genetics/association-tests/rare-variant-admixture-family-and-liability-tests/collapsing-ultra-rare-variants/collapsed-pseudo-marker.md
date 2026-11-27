# Collapsing ultra-rare variants in set-based tests

Let a variant set (a gene, say) contain variants $j = 1, \dots, M$ with genotypes $G_{ij} \in \{0, 1, 2\}$ for individuals $i = 1, \dots, N$ and minor allele counts $\mathrm{MAC}_j = \sum_i G_{ij}$. Fix a threshold $\kappa$ (for instance $\kappa = 10$) and split the set into

$$U = \{ j : \mathrm{MAC}_j \le \kappa \}, \qquad C = \{ j : \mathrm{MAC}_j > \kappa \}.$$

**Collapsed pseudo-marker.** Replace the $|U|$ ultra-rare variants by one surrogate marker whose genotype is the within-individual maximum dosage

$$\tilde{G}_i = \max_{j \in U} G_{ij} \in \{0, 1, 2\},$$

with the default weighting, or $\tilde{G}_i = \max_{j \in U} w_j G_{ij}$ when marker-specific weights $w_j$ are supplied, and run the set-based test on the $|C| + 1$ markers $\{G_{\cdot j}\}_{j \in C} \cup \{\tilde{G}\}$. An individual heterozygous at two different ultra-rare sites gets $\tilde{G}_i = 1$, not $2$, and a homozygote at one site gets $2$. The surrogate records whether, and at what dosage, an individual carries any ultra-rare variant of the set, and it assumes the collapsed variants share a direction and magnitude of effect, the same assumption a burden test makes, but imposed only on the ultra-rare stratum, where individual variants carry no information to contradict it.

Two consequences follow. The effective number of markers drops from $M$ to $|C| + 1$, which reduces both the computation and the number of sparse columns; and the score statistics entering the variance-component test are no longer dominated by singletons and doubletons whose score distributions are far from normal, which is the source of the inflated type I error observed in unbalanced case–control data when tests are restricted to variants of very low frequency.

**Combining strata.** Several maximum-frequency cut-offs and several functional annotations give a family of set tests per gene; their $p$-values are combined into one per gene by the Cauchy combination or by taking the minimum with an appropriate correction. The Cauchy combination is used because the component tests are strongly dependent — they are computed on nested variant sets — and the Cauchy rule is valid without knowledge of that dependence.

## Depends on

- [The SKAT variance-component statistic](../../skat-variance-component-test/continuous-skat-q.md)

## Expansion

The problem being fixed is distributional, not one of power: for a variant seen in a handful of individuals in a sample with a few thousand cases and hundreds of thousands of controls, the score statistic has a discrete, extremely skewed null distribution, and the mixture-of-chi-squares approximation used to obtain a $p$-value from the variance-component statistic is calibrated for a continuum. Collapsing such variants into one maximum-dosage marker produces a marker with a moderate carrier count whose score behaves far closer to the asymptotic reference, so the calibration holds; the cost is that any heterogeneity of effect direction within the collapsed group is averaged away. The gain in practice is large: in whole-exome data on the longest human gene, with three frequency cut-offs and three annotation classes, collapsing plus sparse-matrix arithmetic reduced the computation from thousands of CPU-minutes and tens of gigabytes of memory to minutes and about two gigabytes, which is what makes testing every gene under several masks feasible at biobank scale.

## Sources

- W. Zhou, W. Bi, Z. Zhao et al., "SAIGE-GENE+ improves the efficiency and accuracy of set-based rare variant association tests", Nature Genetics 54 (2022), 1466–1469, main text and Methods (collapsing of variants with MAC ≤ 10; multiple MAF cut-offs and annotations combined by Cauchy or minimum $p$-value), <https://doi.org/10.1038/s41588-022-01178-w>, PMCID PMC9534766.
