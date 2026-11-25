# Fu's $F_s$ statistic

This page covers Fu's $F_s$, a test statistic for neutrality against population growth, hitchhiking and background selection, built from the number of distinct haplotypes in a sample. Under the infinite-alleles model with parameter $\theta$, the law of the number of distinct haplotypes in a sample of $n$ follows from [the Ewens sampling formula](../../population-genetics/ewens-sampling-formula-and-the-chinese-restauran/sum-ewens-prob.md). The statistic transforms the probability of observing at least the observed number of haplotypes, with $\theta$ estimated from the data, by a signed log-odds transformation.

## Expansion

Fix the definition from the source: the haplotype-count tail probability, the transformation, the treatment of the discrete tails, and the estimator of $\theta$. Then state its properties under the neutral model as pages of their own. No exact parameter-free null distribution is claimed.

Prerequisites:

- [Ewens sampling formula](../../population-genetics/ewens-sampling-formula-and-the-chinese-restauran/sum-ewens-prob.md)

## Sources

- Y.-X. Fu, Statistical tests of neutrality of mutations against population growth, hitchhiking and background selection, *Genetics* 147 (1997), 915–925, <https://doi.org/10.1093/genetics/147.2.915>.
