# Genome-wide f-statistic estimation with dependent loci

This node covers the passage from per-site unbiased f-statistic estimators to consistent genome-wide estimates and standard errors when loci are linked. Genome-wide f-statistics are averages $\bar F_L=\frac1L\sum_{i<L}\hat F_i$ of per-site estimators $\hat F_i$ over $L$ correlated loci, and their standard errors are computed by a block jackknife over contiguous blocks of loci.

The obligations of the node are:

1. **Per-site unbiasedness.** Under binomial sampling of $m_X\ge2$ gene copies from each population $X$ at a site with population frequencies $p_X$, the per-site estimators (for example the [unbiased heterozygosity](integral-het-hat.md) and the unbiased $f_2$, $f_3$, $f_4$ estimators of this folder) satisfy $\mathbb E[\hat F_i\mid p]=F_i(p)$, so $\mathbb E\bar F_L=\frac1L\sum_{i<L}\mathbb E F_i$.
2. **Consistency under summable dependence.** If $(\hat F_i)_{i\ge0}$ is second-order stationary with mean $\mu$ and summable autocovariances, then $\bar F_L\to\mu$ in mean square and in probability, by [averages with summable autocovariances](consistency-of-mean-genetic-summaries-under-summ.md); this applies coordinatewise to a vector of f-statistics.
3. **Consistency under independent blocks.** If the loci fall into blocks of fixed size $m$ whose block means $z_1,z_2,\ldots$ are independent and identically distributed and integrable, then $\bar F_{mB}=\frac1B\sum_{b\le B}z_b\to\mathbb E z_1$ almost surely as $B\to\infty$ (strong law of large numbers for the block means). This is the case the expansion must prove first.
4. **Standard errors.** With $B$ blocks, $L\,V_{\mathrm{jack}}$ estimates the asymptotic covariance, by the [delete-one-block jackknife identity](../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/jackknife-covariance-estimation/jack-cov-eq.md) and its [consistency for iid blocks](../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/jackknife-covariance-estimation/ae-tendsto-card-smul-jack-cov.md).

A mixing hypothesis alone does not give item 2; it must be accompanied by bounds that make the autocovariances summable.

## Expansion

A sound expansion states each item as a page of its own, with hypotheses fixed from a source, using the prerequisites listed; the independent-blocks case (item 3) is proved from a finite law-of-large-numbers statement.

Prerequisites:

- [Unbiased heterozygosity](integral-het-hat.md)
- Statistical estimation and likelihood primitives
- [Averages with summable autocovariances converge in mean square](consistency-of-mean-genetic-summaries-under-summ.md)
- [Jackknife covariance as a scaled sample covariance](../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/jackknife-covariance-estimation/jack-cov-eq.md)
- [Strong consistency of the scaled block jackknife covariance](../../../Probability/statistical-estimation/bootstrap-and-the-mallows-metric/jackknife-covariance-estimation/ae-tendsto-card-smul-jack-cov.md)

## Sources

- N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck, T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192(3) (2012), 1065–1093, doi:10.1534/genetics.112.145037, <https://pmc.ncbi.nlm.nih.gov/articles/PMC3522152/>, standard errors for f-statistics by the weighted block jackknife (background).
