# Conditional estimate of second-block effects (COJO)

Let $X_1$ and $X_2$ be real $n \times \iota_1$ and $n \times \iota_2$ matrices ($\iota_1, \iota_2$ finite sets of markers) and let $y \in \mathbb{R}^n$. The conditional estimate of the second-block effects is (Yang et al. 2012)

$$\hat b_{2 \mid 1} = (X_2^\top X_2)^{-1} X_2^\top y - (X_2^\top X_2)^{-1} X_2^\top X_1 (X_1^\top X_1)^{-1} X_1^\top y \in \mathbb{R}^{\iota_2},$$

with the convention that the inverse of a singular matrix is $0$. When both Gram matrices $X_1^\top X_1$ and $X_2^\top X_2$ are invertible, it is the least-squares fit of block 2 to the residual of the least-squares fit of block 1; otherwise it need not be a least-squares fit.

## Sources

- J. Yang et al., *Conditional and joint multiple-SNP analysis of GWAS summary statistics identifies additional variants influencing complex traits*, Nat. Genet. 44 (2012), 369–375.
