# Sparse group-lasso cross-tissue expression imputation

**Model.** Fix a gene and $M$ cis-SNPs. For tissues $i = 1, \dots, P$ let $Y_i \in \mathbb{R}^{N_i}$ be the covariate-adjusted expression levels of the $N_i$ individuals with that tissue sampled, and $X_i \in \mathbb{R}^{N_i \times M}$ their centered genotypes (different tissues may come from overlapping, incomplete subsets of the same donors). Expression follows the multi-tissue linear model

$$Y_i = X_i B_{\cdot i} + \varepsilon_i, \qquad i = 1, \dots, P,$$

with an unknown effect matrix $B \in \mathbb{R}^{M \times P}$ whose column $B_{\cdot i}$ holds the SNP effects in tissue $i$ and whose row $B_{j \cdot}$ holds the effects of SNP $j$ across tissues.

**Estimator.** For tuning parameters $\lambda_1, \lambda_2 \ge 0$,

$$\hat B = \arg\min_{B} \sum_{i=1}^{P} \frac{1}{2N_i}\big\|Y_i - X_i B_{\cdot i}\big\|_2^2 + \lambda_1 \sum_{i=1}^{P} \frac{1}{N_i}\big\|B_{\cdot i}\big\|_1 + \lambda_2 \sum_{j=1}^{M} \big\|B_{j \cdot}\big\|_2 .$$

The objective is convex, so $\hat B$ exists, and it is unique whenever the least-squares part is strictly convex in $B$ (for example when every $X_i$ has full column rank). The imputed expression of a new genotype vector $x$ in tissue $i$ is $x^\top \hat B_{\cdot i}$.

## Remarks

The $\ell_1$ term selects SNPs within each tissue, and its weight $\lambda_1/N_i$ penalizes tissues with small samples more, since they overfit more easily. The row-wise $\ell_2$ (group-lasso) term couples tissues: it either removes SNP $j$ from all tissues ($B_{j\cdot} = 0$) or keeps it in a group, which borrows strength for eQTLs shared across tissues while still allowing tissue-specific signs and magnitudes, since the group penalty does not force equal effects. Together the two penalties form a sparse group lasso. Each tissue enters only through its own observed individuals, so incomplete tissue sampling needs no imputation of missing expression. The parameters $\lambda_1$ (within-tissue sparsity) and $\lambda_2$ (cross-tissue sparsity) are chosen by cross-validation; in the source the joint model raised out-of-sample $R^2$ over single-tissue elastic net most for tissues with small $N_i$.

## Sources

- Y. Hu, M. Li, Q. Lu, H. Weng et al., "A statistical framework for cross-tissue transcriptome-wide association analysis", Nature Genetics 51 (2019), 568–576, Online Methods ("Penalized regression model for cross-tissue expression imputation"), <https://doi.org/10.1038/s41588-019-0345-7>, PMCID PMC6788740.
