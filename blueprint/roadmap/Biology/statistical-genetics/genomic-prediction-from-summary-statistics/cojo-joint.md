# COJO joint estimate

For every real $n \times \iota$ matrix $X$ ($\iota$ a finite set) and every $y \in \mathbb{R}^n$ (Yang et al. 2012; Eq. 5 of the author manuscript),

$$(X^\top X)^{-1} X^\top y = (X^\top X)^{-1} D \hat\beta,$$

where $D = \operatorname{diag}(X^\top X)$ is the [diagonal of the Gram matrix](gram-diag.md), $\hat\beta$ the vector of [marginal estimates](marginal-estimate.md), and the inverse of a singular matrix is $0$. When $X^\top X$ is invertible the left side is the joint least-squares estimate, so it can be computed from the marginal summary statistics and $X^\top X$.

## Sources

- J. Yang et al., *Conditional and joint multiple-SNP analysis of GWAS summary statistics identifies additional variants influencing complex traits*, Nat. Genet. 44 (2012), 369–375; author manuscript PMC3593158, Online Methods, Eq. 5.
