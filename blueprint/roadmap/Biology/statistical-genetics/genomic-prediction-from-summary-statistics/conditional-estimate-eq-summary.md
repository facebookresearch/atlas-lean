# COJO conditional algebraic formula from summary statistics

For all real $n \times \iota_1$ and $n \times \iota_2$ matrices $X_1, X_2$ ($\iota_1, \iota_2$ finite sets) and $y \in \mathbb{R}^n$, the [conditional estimate](conditional-estimate.md) satisfies (Yang et al. 2012; Eq. 17 of the author manuscript)

$$\hat b_{2 \mid 1} = (X_2^\top X_2)^{-1} D_2 \hat\beta_2 - (X_2^\top X_2)^{-1} X_2^\top X_1 (X_1^\top X_1)^{-1} D_1 \hat\beta_1,$$

where $D_i = \operatorname{diag}(X_i^\top X_i)$ is the [diagonal of the Gram matrix](gram-diag.md), $\hat\beta_i$ the vector of [marginal estimates](marginal-estimate.md) of block $i$, and the inverse of a singular matrix is $0$.

## Sources

- J. Yang et al., *Conditional and joint multiple-SNP analysis of GWAS summary statistics identifies additional variants influencing complex traits*, Nat. Genet. 44 (2012), 369–375; author manuscript PMC3593158, Online Methods, Eq. 17.
