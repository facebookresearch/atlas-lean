# Selecting a genetic relationship matrix with principal components as fixed effects

**Setting.** In a genome-wide association study, a linear mixed model gives each candidate SNP a Wald statistic after fitting a random effect with covariance proportional to a genetic relationship matrix (GRM) built from a set of background SNPs. Restricting the GRM to the SNPs most associated with the phenotype raises power when few SNPs are causal, because the random effect then models the actual genetic architecture rather than an infinitesimal one; but the restricted GRM no longer captures population structure, so test statistics are inflated when cases and controls differ in ancestry.

**Statement** (Tucker, Price and Berger 2014). PC-Select fits the mixed model with the top $k$ principal components of the genotype matrix included as fixed effects (a fixed $k = 5$ in the reported analyses, or $k$ chosen by cross-validation or Tracy–Widom statistics), the GRM being built from a cross-validated subset of the most associated background SNPs. The variance components are estimated by restricted maximum likelihood, which projects the genotype matrix onto the orthogonal complement of the fixed-effect space, so the principal components do not simultaneously enter the model as fixed effects and through the random effect. The resulting statistics are calibrated in the presence of stratification, whereas the same subset-GRM model without the components is not: in simulations with two populations at $F_{ST} = 0.05$ and a fraction $0.005$ of SNPs causal, the genomic-control inflation factor was $1.01 \pm 0.01$ with the components and $1.26 \pm 0.03$ without, while the mean Wald statistic at causal SNPs was unchanged by stratification with the components ($16.3 \pm 0.1$ with and without) and reduced without them ($14.3 \pm 0.2$ versus $16.4 \pm 0.1$). The asymptotic cost is that of the underlying mixed model, quadratic in the number of individuals and linear in the number of markers.

## Depends on

- [Residual as projection onto the orthogonal complement](../adjusted-eq-star-projection-orthogonal.md)
- [Span of the top axes of variation](../top-axes-span.md): the top $k$ principal components used as fixed effects
- [Genetic relationship matrix](../../greml-and-haseman-elston-estimation-of-snp-herit/grm.md): the GRM built from the selected background SNPs
- [Variance components of the linear mixed model](../../bolt-lmm-mixed-model-association/model.md): the mixed model with a random effect of covariance proportional to the GRM
- [REML projection matrix](../../greml-and-haseman-elston-estimation-of-snp-herit/reml-proj.md): restricted maximum likelihood on error contrasts orthogonal to the fixed effects
- [Population genomic-control factor of the LD-score model](../../association-tests/genomic-control/lambda-gc.md): the genomic-control inflation factor reported

## Expansion

Ancestry enters the phenotype through a few axes of variation, which the leading principal components span; a GRM built from a small set of associated SNPs does not span them, since association ranking selects for phenotypic correlation and not for differentiation. Including the components as fixed effects removes the ancestry signal from both the phenotype and the genotypes, and restricted maximum likelihood makes the removal exact for the variance-component estimate by working in the orthogonal complement of the fixed-effect space, avoiding the ill-posedness that arises when structure is modeled twice. The components also denoise the selection step: the SNPs chosen in the presence of stratification are more often genuinely associated, so fewer are needed (about $20$ versus about $240$ in the reported simulations). Fixed-effect components do not account for family or cryptic relatedness, for which the subset GRM itself must carry the signal.

## Sources

- G. Tucker, A. L. Price and B. Berger, "Improving the power of GWAS and avoiding confounding from population stratification with PC-Select", Genetics 197 (2014), 1045–1049, Tables 1–2 and Figure 1, <https://doi.org/10.1534/genetics.114.164285>, PMCID PMC4096359.
