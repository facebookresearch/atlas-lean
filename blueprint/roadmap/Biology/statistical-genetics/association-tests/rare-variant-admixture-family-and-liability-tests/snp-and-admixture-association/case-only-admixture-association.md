# Case-only admixture association

Let the sample be cases from a two-way admixed population with ancestral populations $A$ and $E$. For case $i$ let $\theta_i \in [0, 1]$ be the genome-wide proportion of $E$ ancestry and $N_i \in \{0, 1, 2\}$ the number of $E$ chromosomes at a candidate locus. Under the null the local ancestry at any locus is distributed as the genome-wide ancestry, $N_i \sim \mathrm{Binomial}(2, \theta_i)$. Under the alternative a disease-associated variant carried preferentially on one ancestry's chromosomes deviates the local ancestry in cases; parameterize the deviation by an **ancestry odds ratio** $\Omega > 0$, the multiplicative risk per $E$ allele, so that for case $i$

$$\Pr(N_i = 2) \propto \theta_i^2 \,\Omega^2, \qquad \Pr(N_i = 1) \propto 2\theta_i(1 - \theta_i)\,\Omega, \qquad \Pr(N_i = 0) \propto (1 - \theta_i)^2,$$

normalized by $\big(\theta_i \Omega + 1 - \theta_i\big)^2$. The likelihood is $L(\Omega) = \prod_i \Pr(N_i \mid \theta_i, \Omega)$ and the statistic is

$$\chi^2_{\mathrm{ADM}} = 2 \log \frac{\max_{\Omega} L(\Omega)}{L(1)} \;\sim\; \chi^2_1 \text{ under } \Omega = 1 .$$

No controls enter, which is the point: the comparison is between the local ancestry at the candidate locus and the same individuals' ancestry elsewhere in the genome, so control sampling noise does not contribute. The test is only as good as the local-ancestry inference: a method that produces systematic deviations of average local ancestry in control data would create signal here, so the score requires an inference method validated against that failure mode.

**Variance correction.** Deviations from random mating and correlated errors in local-ancestry calls inflate the variance of the average local ancestry across the genome beyond the binomial value. Modelling the per-locus average local ancestry as normal with mean determined by $\Omega$ and standard deviation estimated empirically across the genome gives a corrected statistic; it amounts to dividing the uncorrected statistic by the genomic-control inflation factor computed from the empirical variance.

**Multiple-testing scale.** Because ancestry segments are long, the number of effectively independent hypotheses in a genome-wide admixture scan is of order a thousand rather than a million, so the appropriate significance threshold is near $10^{-5}$ rather than $5 \times 10^{-8}$.

## Depends on

- [Genomic control inflation factor](../../genomic-control/lambda-gc.md)

## Expansion

The per-individual probabilities are the tilt of a binomial by a multiplicative factor per $E$ allele, the same construction as tilting an allele frequency by an odds ratio, applied to ancestry instead of genotype; conditioning on $\theta_i$ removes the dependence on how admixed each individual is, so population structure within the admixed sample is absorbed. The information content of the test is concentrated at loci where the ancestral populations differ in causal-allele frequency: when they do not, $\Omega = 1$ even under a true association, and the test has no power. That complementarity with a genotype-based test — one strong exactly where the other is weak — is why combining the two likelihoods is worthwhile.

## Sources

- B. Pasaniuc, N. Zaitlen, G. Lettre et al., "Enhanced statistical tests for GWAS in admixed populations: assessment using African Americans from CARe and a Breast Cancer Consortium", PLoS Genetics 7 (2011), e1001371, Methods ("ADM: admixture association using cases only" and "Incorporating the empirical variance of the average ancestry estimates"), <https://doi.org/10.1371/journal.pgen.1001371>, PMCID PMC3080860.
