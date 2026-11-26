# Predicted genetic variance of a cross and the usefulness criterion

Let two outbred diploid parents $P_1, P_2$ be genotyped and phased at $p$ biallelic loci, with haplotype matrices $H_{P}\in\{0,1\}^{2\times p}$ (entry $1$ if the counted allele is present) and within-parent allele frequencies $\mathbf p_{P} = \tfrac12 H_P^\top\mathbf 1$. Let $c$ be the $p\times p$ matrix of pairwise recombination fractions from a genetic map. Define

$$D_P^{\mathrm{haplos}} = \tfrac12 H_P^\top H_P - \mathbf p_P\mathbf p_P^\top, \qquad D_P^{\mathrm{gametes}} = (\mathbf 1\mathbf 1^\top - 2c)\odot D_P^{\mathrm{haplos}},$$

$$D = D_{P_1\times P_2}^{\mathrm{genotypes}} = D_{P_1}^{\mathrm{gametes}} + D_{P_2}^{\mathrm{gametes}},$$

the expected covariance matrix of allele dosages among full-sib progeny, where $\odot$ is the Hadamard product.

**Cross variances.** With allele-substitution effects $\alpha$ and dominance effects $d$ (from the additive–dominance marker model $y = X\beta + Z\alpha + Wd + \epsilon$ with centered genotype codings), the predicted within-family variances of breeding value, dominance deviation and total genetic value are

$$\hat\sigma^2_{BV} = \alpha^\top D\alpha, \qquad \hat\sigma^2_{DD} = d^\top(D\odot D)\,d, \qquad \hat\sigma^2_{TGV} = \hat\sigma^2_{BV} + \hat\sigma^2_{DD}.$$

The predicted family mean breeding value is $\mu_{BV} = (\mathrm{GEBV}_{P_1} + \mathrm{GEBV}_{P_2})/2$.

**Usefulness criterion.** For within-family truncation selection with standardized selection intensity $i$, the expected mean of the selected progeny is

$$UC = \mu + i\,\sigma;$$

for parent selection $UC_{\mathrm{parent}} = \mu_{BV} + i_{RS}\,\sigma_{BV}$, and for variety selection $UC_{\mathrm{variety}} = \mu_{TGV} + i_{VDP}\,\sigma_{TGV}$, with possibly different intensities in the recurrent-selection and variety-development stages. For a selection index $I = \sum_t b_tT_t$, the cross variance is $\sum_{t,t'}b_tb_{t'}\hat\sigma_{tt'}$ with trait covariances $\hat\sigma_{tt'} = \alpha_t^\top D\alpha_{t'}$.

## Depends on

- [Response to selection](../breeder-s-equation/response.md)

## Expansion

A gamete of parent $P$ carries at locus $k$ the allele of one of $P$'s two haplotypes chosen at random; for loci $k, l$ the gametic covariance equals the haplotypic covariance $D^{\mathrm{haplos}}_{P,kl}$ times the probability $1-2c_{kl}$ that phase is preserved minus that it is broken, i.e. $(1 - c_{kl}) - c_{kl}$. The two parental gametes are independent, so the progeny dosage covariance is the sum. The variance of the linear predictor $\alpha^\top x$ is $\alpha^\top D\alpha$; the dominance term uses $D\odot D$ following the formula for dominance variance under linkage disequilibrium among full-sibs. For a normally distributed family, the mean above the truncation point is $\mu + i\sigma$.

## Sources

- Marnin D. Wolfe, Ariel W Chan and Peter Kulakow, "Genomic mating in outbred species: predicting cross usefulness with additive and total genetic covariance matrices", Genetics (2021), <https://doi.org/10.1093/genetics/iyab122> (PMC8570794). Methods, "Formulation of genomic predictions and selection criteria", including Table 1.
