# Recombination-stratified estimator of the non-crossover rate

**Target.** Let $R$ be the probability that a given base pair lies inside a non-crossover gene-conversion tract in one meiosis, equivalently the expected fraction of the genome converted per meiosis. If $N$ tracts of mean length $l$ occur per meiosis in a genome of length $G$, then $R = Nl/G$.

**Naive estimator.** From pedigree transmissions, if $n$ of $m$ heterozygous (informative) sites are observed to be converted, then $\hat R = n/m$, unbiased provided the informative sites are a random sample of the genome with respect to recombination rate.

**Stratified estimator.** Genotyping arrays over-represent regions of high recombination, where conversion is more frequent, so partition the genome into bins $b = 1,\dots,B$ of recombination rate, with $n_b$ converted sites out of $m_b$ informative sites in bin $b$ and $w_b$ the fraction of the autosomal genome in bin $b$ ($\sum_b w_b = 1$). Then

$$\hat R = \sum_{b=1}^{B} w_b\,\frac{n_b}{m_b},$$

which is consistent for $R$ under the weaker assumption that informative sites are representative within each bin. Confidence intervals come from a block bootstrap over large genomic blocks, which preserves the correlation between nearby sites.

## Expansion

The weight $w_b$ replaces the ascertained share $m_b/\sum_b m_b$ by the true genomic share, which is exactly the reweighting needed when the sampling probability of a site depends only on its bin. Applied to 97 non-crossover sites among 12.1 million informative sites in human three-generation pedigrees, the stratified estimate is $\hat R = 5.9\times10^{-6}$ per base pair per meiosis (95% confidence interval $4.6\times10^{-6}$ to $7.4\times10^{-6}$ from 40,000 bootstrap samples with 10 Mb blocks), consistent with sperm-typing estimates obtained from $R = Nl/G$. Because an array detects a tract only when it contains an informative site, longer tracts are over-sampled, so the same data bound tract lengths (roughly 100 to 1000 base pairs here) but do not identify their mean without further assumptions.

## Sources

- A. L. Williams, G. Genovese, T. Dyer et al., "Non-crossover gene conversions show strong GC bias and unexpected clustering in humans", eLife (2015), Results ("Rate of NCO events and their location in the two sexes" and "NCO gene conversion tract lengths"), <https://doi.org/10.7554/eLife.04637>.
