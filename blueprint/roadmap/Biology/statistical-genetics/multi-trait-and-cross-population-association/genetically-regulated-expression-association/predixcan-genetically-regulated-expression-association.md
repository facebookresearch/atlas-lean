# PrediXcan genetically regulated expression association

**Additive expression model.** In a reference transcriptome sample, model the expression of gene $g$ as

$$Y_g = \sum_k w_{k,g} X_k + \epsilon,$$

where $X_k \in \{0,1,2\}$ is the reference-allele count of marker $k$ (in practice, markers within 1 Mb of the gene), $w_{k,g}$ its effect, and $\epsilon$ the non-genetic component, independent of the genotypes. The sum $\mathrm{GReX}_g = \sum_k w_{k,g} X_k$ is the **genetically regulated expression**.

**Prediction weights.** Estimate $\hat w_{k,g}$ in the reference data by a penalized regression; PrediXcan uses the elastic net (glmnet with mixing parameter $\alpha = 0.5$), which minimizes

$$\frac{1}{2n}\Bigl\| \mathbf Y_g - \sum_k w_k \mathbf X_k \Bigr\|_2^2 + \lambda\Bigl(\frac{1-\alpha}{2}\|w\|_2^2 + \alpha \|w\|_1\Bigr),$$

with $\lambda$ chosen by cross-validation. LASSO ($\alpha = 1$) and polygenic scores of marginal eQTL estimates are alternatives.

**Association test.** In a GWAS sample with genotypes but no expression, impute

$$\widehat{\mathrm{GReX}}_g = \sum_k \hat w_{k,g} X_k$$

and test the phenotype against $\widehat{\mathrm{GReX}}_g$ by linear, logistic or Cox regression, or a rank correlation, one test per gene.

**Accuracy ceiling.** The cis-heritability of expression, estimated by the mixed model $Y = Xb + G_{\mathrm{local}} + e$ with $\operatorname{var}(Y) = A_{\mathrm{local}}\sigma^2_{\mathrm{local}} + I\sigma_e^2$ and $A_{\mathrm{local}}$ the genetic relationship matrix of local SNPs, bounds the attainable prediction $R^2$.

## Depends on

- [Genetic relationship matrix](../../greml-and-haseman-elston-estimation-of-snp-herit/grm.md)

## Expansion

The test targets one mechanism: genetic variation acting on the phenotype through the expression of a gene. Because $\widehat{\mathrm{GReX}}_g$ depends on genotype only, it is unaffected by reverse causation from the trait to expression and by environmental confounding of expression. Aggregating cis-SNPs into one predictor reduces the multiple-testing burden to the number of genes. The error in $\hat w$ attenuates the estimated effect toward zero but leaves the null distribution intact, so the method is valid for discovery. Under fixed weights, the individual-level regression slope is approximated from summary statistics by the burden $Z$-score. In whole blood, the elastic-net cross-validated $R^2$ averaged $0.137$ against a mean cis-heritability of $0.153$.

## Sources

- E. R. Gamazon, H. E. Wheeler, K. P. Shah, et al., "A gene-based association method for mapping traits using reference transcriptome data", *Nature Genetics* (2015), <https://doi.org/10.1038/ng.3367> (PMC4552594; Methods, Equations (1) and (2), sections "Additive model for gene expression traits" and "Estimation of the genetic component of gene expression levels").
