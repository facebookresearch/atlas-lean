# First principal component of polygenic scores across thresholding settings (PRS-PCA)

Let $G_{ij}$ be individual $i$'s allele count at SNP $j$ ($i = 1, \dots, N$; $j = 1, \dots, J$). For $K$ pruning-and-thresholding settings $k$, let $\beta_{jk}$ be the weight of SNP $j$ under setting $k$: the source-GWAS effect estimate $\hat\beta_j$ if SNP $j$ survives clumping and the $p$-value threshold of setting $k$, and $0$ otherwise. The polygenic scores are $\mathrm{PRS}_{ik} = \sum_{j=1}^J G_{ij}\beta_{jk}$, with sample mean $\mu_k$ and standard deviation $\sigma_k$. Stack the standardized scores $(\mathrm{PRS}_{ik} - \mu_k)/\sigma_k$ into an $N \times K$ matrix and let $w = (w_1, \dots, w_K)$ be its first principal-component loading vector (unit norm). The **PRS-PC1** score is

$$\mathrm{PRS\text{-}PC1}_i = \sum_{k=1}^K w_k \frac{\mathrm{PRS}_{ik} - \mu_k}{\sigma_k} = \sum_{j=1}^J G_{ij} \Bigl(\sum_{k=1}^K \frac{w_k \beta_{jk}}{\sigma_k}\Bigr) - \sum_{k=1}^K \frac{w_k \mu_k}{\sigma_k},$$

so it is itself a polygenic score with SNP weights $\sum_k w_k\beta_{jk}/\sigma_k$. The weights are chosen without using the target phenotype. One association test of the phenotype on PRS-PC1 therefore needs no multiple-testing correction over the $K$ settings, unlike choosing the best-fitting setting, which inflates type I error unless corrected by permutation.

## Depends on

- [Squared accuracy of a polygenic score](accuracy-sq.md)

## Expansion

The first principal component maximizes the variance of a unit-norm combination of the standardized scores, that is, the top eigenvector of their correlation matrix. When the scores are highly correlated across thresholds, it is close to an equal-weight average. Substituting the definition of $\mathrm{PRS}_{ik}$ and exchanging the sums over $k$ and $j$ gives the per-SNP weights. Because $w$ depends only on the genotypes and the source GWAS, PRS-PC1 is fixed before the phenotype is examined, so the usual null distribution of the association test applies.

## Sources

- B. J. Coombes, A. Ploner, S. E. Bergen et al., *A principal component approach to improve association testing with polygenic risk scores*, Genet. Epidemiol. 44 (2020), <https://doi.org/10.1002/gepi.22339>, PMCID PMC7722089, Methods, "Polygenic risk scores" and "PRS-PCA approach" (standardized PRS matrix, PCA and SNP-level weight representation), as read from the authors' preprint version.
