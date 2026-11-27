# Poisson-binomial test for frequently mutated regulatory elements

Let a cohort consist of $S$ tumour samples and let the candidate noncoding regions be regulatory
elements indexed by $i$, element $i$ having length $n_i$ base pairs. For sample $k$, let

$$p_k = \frac{n_k}{n_{\mathrm{cov}}}$$

be its global background mutation rate per base pair, estimated as the number $n_k$ of noncoding
single-nucleotide variants called in that sample divided by the total covered length
$n_{\mathrm{cov}}$ of the regions of interest. Under the null hypothesis that mutations fall
independently and uniformly at that rate, the number $X_i \in \{0, 1, \dots, S\}$ of samples
carrying at least one mutation in element $i$ has the Poisson-binomial distribution with success
probability vector

$$\Bigl[\,1 - (1 - p_k)^{n_i}\,\Bigr]_{k=1,\dots,S},$$

each entry being the probability that sample $k$ carries at least one of $n_i$ independent mutable
sites mutated. An element is called frequently mutated when the observed $X_i$ is in the upper tail
of this distribution, after correction for multiple testing.

## Depends on

- [Poisson-binomial mass function](../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf.md)
- [Upper tail of the Poisson-binomial law](../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-tail.md)

## Proof depends on

- [Distribution of a sum of independent Bernoulli variables](../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/bernoulli-sum-pmf.md)

## Remarks

Counting samples rather than mutations makes the statistic robust to a single hypermutated sample
dominating one element, and the Poisson-binomial, rather than a binomial, is needed because the
per-sample rates $p_k$ differ by orders of magnitude across a cohort. Element length enters only
through $1 - (1-p_k)^{n_i}$, so long elements are automatically expected to be hit more often.

## Sources

- R. I. Corona et al., "Non-coding somatic mutations converge on the PAX8 pathway in ovarian
  cancer", Nature Communications 11 (2020) 2020, Methods,
  <https://doi.org/10.1038/s41467-020-15951-0> (PMC7181647).
