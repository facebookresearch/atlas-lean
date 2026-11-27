# Sampling and covering probabilities for insert-length detection of indels

In paired-end sequencing, fragment (insert) lengths follow a Gaussian library distribution $\mathcal{L} \sim N(\lambda, \sigma^2)$. An insertion or deletion structural variant (ISV, DSV) of size $\delta$ at a site shifts the apparent length of every insert spanning the site by $\delta$ in one direction. Let $K$ be the number of inserts spanning a candidate site and $\mathcal{M}$ their mean apparent length.

**Theorem (sampling probability).** Under the null hypothesis $h_0$ of no variant of size $\delta$, given $K = k$ spanning inserts, $\mathcal{M} \sim N(\lambda, \sigma^2/k)$, so

$$P\big(\lambda - \delta \le \mathcal{M} \le \lambda + \delta \mid k\big) = \operatorname{erf}\!\Big(\frac{\delta\sqrt{k}}{\sigma\sqrt2}\Big)$$

for the two-tailed test of ISV $\cup$ DSV, and

$$P(\mathcal{M} \le \lambda + \delta \mid k) = P(\lambda - \delta \le \mathcal{M} \mid k) = \tfrac12\Big[1 + \operatorname{erf}\!\Big(\frac{\delta\sqrt{k}}{\sigma\sqrt2}\Big)\Big]$$

for the one-tailed tests of each type separately.

**Covering.** A single insert covers the site with a small Bernoulli probability determined by the genome length $G$, the read length, the insert length (at least a minimum admissible length $m$ that differs between insertions and deletions, since reads must flank the variant) and zygosity (homozygous variants are seen on both haplotypes, heterozygous on one). With $N$ inserts processed, $K$ is therefore asymptotically Poisson with a rate proportional to $N$ times this coverage probability, the Gaussian length distribution being integrated over admissible lengths.

**Theorem (false positives).** If $C$ is the event that the sample mean falls in the confidence interval, then

$$P(C) = \sum_{k \ge 1} P(K = k)\, P(C \mid k),$$

and calling a variant whenever $\mathcal{M} \notin C$ has false-positive rate $\alpha = 1 - P(C)$. The **standard model** uses separate one-tailed intervals with type-specific $m$ for ISV and DSV; the **symmetric model** uses the two-tailed interval and treats them as opposites.

## Depends on

- [Law of the Gaussian sample mean](../../../../Probability/linear-models-multivariate/cochran-s-theorem/has-law-sample-mean.md)

## Proof depends on

- [Analytic core of Poisson convergence](../../../../Probability/central-limit-theorems/poisson-limit-theorem/elem-symm-poly-tendsto-poisson.md)

## Expansion

The sampling theorem is the Gaussian distribution of a sample mean: substituting $x = (\ell - \lambda)\sqrt{k}/\sigma$ turns the interval probability into an error function. Because ISV detection disallows reads falling inside the inserted sequence, fewer inserts are admissible around insertions than around deletions, so the two variant types have different power and error profiles, contrary to the common symmetric assumption. Combining the binomial (asymptotically Poisson) number of spanning inserts with the conditional sampling probability gives a priori detection power and error rates for planning sequencing depth and choosing library size and spread.

## Sources

- M. C. Wendl and R. K. Wilson, "Statistical aspects of discerning indel-type structural variation via DNA sequence alignment", BMC Genomics 10 (2009), 359, Theorem 1, Lemma 2, Theorem 4, Corollaries 5–6 and Eqs. (1)–(8), <https://doi.org/10.1186/1471-2164-10-359>, PMCID: PMC2748092.
