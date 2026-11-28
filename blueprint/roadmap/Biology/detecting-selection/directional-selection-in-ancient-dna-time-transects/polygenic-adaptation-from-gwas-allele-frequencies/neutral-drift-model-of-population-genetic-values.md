# Neutral drift model of population genetic values

Let $L$ biallelic loci have additive effect estimates $\alpha_\ell$ (per copy of the trait-increasing allele) from a genome-wide association study, and let $\hat p_{m\ell}$ be the sample frequency of that allele at locus $\ell$ in population $m = 1, \dots, M$.

**Estimated genetic value.** The mean additive genetic value of population $m$ is estimated by

$$\hat Z_m = 2 \sum_{\ell=1}^{L} \alpha_\ell\, \hat p_{m\ell}, \qquad \hat{\mathbf Z} = (\hat Z_1, \dots, \hat Z_M).$$

**Drift model.** Under neutrality, the frequency vector at a locus with ancestral frequency $\epsilon_\ell$ is approximated as

$$\vec p_\ell \sim \mathrm{MVN}\bigl(\epsilon_\ell \mathbf 1,\ \epsilon_\ell(1 - \epsilon_\ell)\, \mathbf F\bigr),$$

where $\mathbf F$ is a positive definite $M \times M$ matrix shared by all loci (for small values, inbreeding coefficients on the diagonal and population kinships off it, relative to the ancestral population). Unlinked loci drift independently, so

$$\hat{\mathbf Z} \sim \mathrm{MVN}\bigl(\mu \mathbf 1,\ 2 V_A \mathbf F\bigr), \qquad \mu = 2\sum_\ell \alpha_\ell \epsilon_\ell, \quad V_A = 2 \sum_\ell \alpha_\ell^2 \epsilon_\ell (1 - \epsilon_\ell),$$

with $V_A$ the additive genetic variance contributed by these loci in the ancestral population.

**Standardization.** In practice $\mu$ is replaced by the mean of $\hat{\mathbf Z}$, losing one degree of freedom: let $\mathbf Z'$ be the mean-centered vector with the last entry dropped and $\mathbf F$ the correspondingly centered $(M-1) \times (M-1)$ matrix, estimated from matched genome-wide control SNPs. With the Cholesky factorization $\mathbf F = \mathbf C \mathbf C^\top$,

$$\mathbf X = \frac{\mathbf C^{-1} \mathbf Z'}{\sqrt{2 V_A}} \sim \mathrm{MVN}(\mathbf 0, \mathbf I_{M-1})$$

under the null. A linear regression of $\mathbf X$ on the identically transformed, centered environmental variable tests for an environmental correlation of genetic values.

## Expansion

$\hat Z_m$ is a fixed linear combination of allele frequencies, so its law under the multivariate normal drift model is again multivariate normal, with covariance $\sum_\ell 4\alpha_\ell^2 \epsilon_\ell(1-\epsilon_\ell)\mathbf F = 2V_A\mathbf F$. Even when drift at single loci is not Gaussian, the sum over many loci is approximately normal by the central limit theorem. Under neutrality the deviations of allele frequencies are uncorrelated with the effect signs, so false positives arise only if GWAS ascertainment correlates $\alpha_\ell$ with population frequency deviations, as with uncorrected stratification in the discovery GWAS. The transformation by $\mathbf C^{-1}$ maps the populations onto a star-shaped tree with equal branches, after which standard i.i.d. tests apply.

## Sources

- J. J. Berg and G. Coop, "A Population Genetic Signal of Polygenic Adaptation", *PLoS Genetics* 10 (2014), e1004412, <https://doi.org/10.1371/journal.pgen.1004412> (PMC4125079; Equations (1)–(9), sections "Estimating Genetic Values with GWAS Data" to "Environmental Correlations").
