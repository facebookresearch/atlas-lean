# Marginal least-squares estimate of a marker effect

Let $X$ be a real $n \times \iota$ genotype matrix ($\iota$ a finite set of markers) with columns $x_j$, and let $y \in \mathbb{R}^n$. The marginal estimate of marker $j$ is (Yang et al. 2012)

$$\hat\beta_j = \frac{x_j^\top y}{x_j^\top x_j},$$

with the convention $x/0 = 0$ (so $\hat\beta_j = 0$ for a zero column). It is the single-marker least-squares estimate without intercept.

## Sources

- J. Yang et al., *Conditional and joint multiple-SNP analysis of GWAS summary statistics identifies additional variants influencing complex traits*, Nat. Genet. 44 (2012), 369–375.
