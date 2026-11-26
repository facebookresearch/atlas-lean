# GC-biased transmission at non-crossover sites

**Model.** Consider heterozygous sites with one AT allele and one GC allele that lie inside an observed non-crossover gene-conversion tract. Under Mendelian transmission with unbiased repair of the AT/GC heteroduplex, each converted site transmits the GC allele with probability $1/2$, independently across sites, so the number $X$ of GC transmissions among $n$ such sites is $\mathrm{Binomial}(n, 1/2)$.

**Test.** GC-biased gene conversion is the alternative $p = P(\text{GC transmitted}) > 1/2$, tested by the exact binomial test on $X$; the maximum-likelihood estimate is $\hat p = X/n$ with the usual binomial confidence interval. Sites whose conversion may be driven by initiation bias (those in a recombination-initiation motif, where the allele matching the motif is under-transmitted) are excluded, since that mechanism also perturbs transmission but acts through double-strand-break formation rather than repair.

## Depends on

- [Recombination-stratified estimator of the non-crossover rate](recombination-stratified-estimator-of-the-non-crossover-rate.md)

## Expansion

Independence across sites requires one conversion event per site, so clustered tracts covering several sites must be counted once. In human pedigrees, $63$ of $92$ non-crossover sites transmitted the G or C allele ($68\%$, 95% confidence interval $58\%$–$78\%$, two-sided binomial $P = 5.1\times10^{-4}$), with no detectable difference between CpG and non-CpG sites or between the sexes. Over evolutionary time such a transmission bias acts like weak directional selection favouring GC alleles in regions of high recombination, raising their fixation probability without any fitness difference.

## Sources

- A. L. Williams, G. Genovese, T. Dyer et al., "Non-crossover gene conversions show strong GC bias and unexpected clustering in humans", eLife (2015), Results ("GC-biased gene conversion"), <https://doi.org/10.7554/eLife.04637>.
