# Q_X excess-variance test for polygenic adaptation

In the [neutral drift model of population genetic values](neutral-drift-model-of-population-genetic-values.md), let $\mathbf Z'$ be the centered vector of estimated genetic values of $M$ populations (one entry dropped), $\mathbf F$ the centered drift covariance and $V_A$ the ancestral additive variance contributed by the GWAS loci.

**Definition.**

$$Q_X = \mathbf X^\top \mathbf X = \frac{\mathbf Z'^{\top}\, \mathbf F^{-1}\, \mathbf Z'}{2 V_A}.$$

**Null distribution.** Under neutral drift $Q_X \sim \chi^2_{M-1}$. Upper-tail values indicate excess among-population variance in genetic values, consistent with local adaptation; lower-tail values indicate a deficit, consistent with stabilizing selection toward a shared optimum. $Q_X$ is, up to constants, the negative log-likelihood of $\mathbf Z'$ under the neutral model.

**Relation to $Q_{ST}$.** For a star-shaped population tree with equal branches ($\mathbf F$ diagonal with common value $F_{ST}$), $Q_X$ reduces to a multiple of the ratio $\hat Q_{ST}/F_{ST}$, where $\hat Q_{ST}$ is the among-population fraction of additive variance estimated from the genetic values (the exact form is the source's Equation (11)). For a neutral additive trait $Q_{ST} = F_{ST}$, so this is the phenotypic analog of the Lewontin–Krakauer $F_{ST}$ test, and $Q_X$ extends it to arbitrary population structure.

**Decomposition.** Expanding $\mathbf Z'$ as a weighted sum of (transformed) allele frequencies splits $Q_X$ into an $F_{ST}$-like term, the $\alpha_\ell^2$-weighted sum of among-population variances of individual loci, and an LD-like term, the weighted sum of among-population covariances between pairs of GWAS loci. The LD-like term has expectation zero under neutrality and captures the coordinated allele-frequency shifts that selection on the trait produces.

## Depends on

- [Neutral drift model of population genetic values](neutral-drift-model-of-population-genetic-values.md)

## Expansion

Since $\mathbf X = \mathbf C^{-1}\mathbf Z'/\sqrt{2V_A}$ has i.i.d. standard normal entries under the null, the sum of their squares is $\chi^2_{M-1}$. Power comes mainly from the LD-like term: selection moves trait-increasing alleles at many loci in the same direction in the same populations, a covariance that single-locus outlier scans cannot see. In practice the null is also calibrated empirically by recomputing $Q_X$ on matched sets of random SNPs, and the empirical and $\chi^2$ nulls agree closely. Conditional multivariate normal distributions then locate the populations driving a signal, through a $Z$-score of each population's genetic value given the others.

## Sources

- J. J. Berg and G. Coop, "A Population Genetic Signal of Polygenic Adaptation", *PLoS Genetics* 10 (2014), e1004412, <https://doi.org/10.1371/journal.pgen.1004412> (PMC4125079; Equations (10)–(14), sections "Excess Variance Test" and "Identifying Outlier Populations").
