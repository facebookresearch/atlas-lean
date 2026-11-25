# Residual stratification produces covariance between a polygenic score and ancestry

Let $A$ be a real ancestry coordinate of a randomly drawn individual with $\operatorname{Var}A=1$, and let $G_1,\ldots,G_J$ be the individual's genotype counts at $J$ loci, square integrable. Write

$$\Delta_j=\operatorname{Cov}(G_j,A),\qquad j=1,\ldots,J,$$

for the allele-frequency differentiation of locus $j$ along the ancestry axis. Let $c_1,\ldots,c_J$ be real loadings of the loci on that axis and $b\in\mathbb R$. Suppose the estimated effects are

$$\hat\beta_j=\beta_j+b\,c_j,$$

where the true effects $\beta_j$ are random, independent of the genotypes and of the population, with $\mathbb E\beta_j=0$ (neutrality: no systematic relation between effects and frequency differences). Let $\mathrm{PRS}=\sum_j\hat\beta_jG_j$ and let $\operatorname{Cov}_{\mathrm{pop}}$ denote covariance over individuals for fixed effects. Then

$$\mathbb E_\beta\bigl[\operatorname{Cov}_{\mathrm{pop}}(\mathrm{PRS},A)\bigr]=b\sum_{j=1}^Jc_j\Delta_j .$$

In particular, with no residual stratification ($b=0$) the expected covariance is $0$; if $b\ne0$ and $\sum_jc_j\Delta_j\ne0$ (for example $c_j=\Delta_j$ with some $\Delta_j\ne0$), the score covaries with ancestry in expectation although no selection acts on the trait.

## Proof depends on

- [Covariance induced by population stratification](population-stratification-creates-spurious-assoc.md)

## Expansion

A full proof page must establish the following.

- Bilinearity: for fixed effects, $\operatorname{Cov}_{\mathrm{pop}}(\mathrm{PRS},A)=\sum_j\hat\beta_j\Delta_j$; taking expectation over $\beta$ with $\mathbb E\beta_j=0$ leaves $b\sum_jc_j\Delta_j$.
- The zero-bias case under neutrality.
- That the non-vanishing condition $\sum_jc_j\Delta_j\ne0$ is needed: with $b\ne0$ and loadings orthogonal to the differentiation vector the expectation is $0$.
- The relation with the single-locus [covariance induced by population stratification](population-stratification-creates-spurious-assoc.md), which explains how residual stratification enters $\hat\beta_j$ as a shift proportional to $c_j$.

## Sources

- J. J. Berg et al., *Reduced signal for polygenic adaptation of height in UK Biobank*, eLife 8 (2019), e39725, doi:10.7554/eLife.39725; M. Sohail et al., *Polygenic adaptation on height is overestimated due to uncorrected stratification in genome-wide association studies*, eLife 8 (2019), e39702, doi:10.7554/eLife.39702 (background: stratification inflating polygenic adaptation signals).
