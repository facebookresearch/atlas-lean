# Profile likelihood of a single causal variant from association z-scores

Let $Z = (z_1,\dots,z_M)^\top$ be association z-scores at $M$ SNPs whose pairwise genotype correlations form a positive definite LD matrix $\Sigma$ (so $\Sigma_{ii} = 1$). Suppose SNP $c$ is the only causal variant, with non-centrality $\lambda_c$, so that each $z_i \sim N(\Sigma_{ic}\lambda_c, 1)$ and jointly

$$Z \sim N(\lambda_c\,\Sigma e_c,\; \Sigma),$$

with $e_c$ the $c$-th standard basis vector.

**Claim.** The log-likelihood $\log L(Z; c, \lambda)$ is maximized over $\lambda \in \mathbb R$ at $\hat\lambda_c = z_c$, and the profile log-likelihood of SNP $c$ being causal is

$$\log L(Z; c, \hat\lambda_c) = \tfrac12\left(-Z^\top\Sigma^{-1}Z + z_c^2\right) - \tfrac12\log\!\left((2\pi)^M|\Sigma|\right).$$

Consequently, for two candidate causal SNPs $i$ and $j$, $\log L(Z; i, \hat\lambda_i) - \log L(Z; j, \hat\lambda_j) = \tfrac12(z_i^2 - z_j^2)$: under the single-causal-variant model, candidates are ranked by their marginal $\chi^2$ statistics.

## Proof sketch

Expanding the Gaussian exponent, $(Z - \lambda\Sigma e_c)^\top\Sigma^{-1}(Z - \lambda\Sigma e_c) = Z^\top\Sigma^{-1}Z - 2\lambda e_c^\top Z + \lambda^2\Sigma_{cc} = Z^\top\Sigma^{-1}Z - 2\lambda z_c + \lambda^2$. This is a quadratic in $\lambda$ minimized at $\lambda = z_c$ with minimum $Z^\top\Sigma^{-1}Z - z_c^2$; inserting it into the normal log-density gives the claim. The terms not involving $c$ cancel in likelihood ratios, which is why colocalization and fine-mapping statistics built on this model reduce to functions of $z_c^2$.

## Sources

- S. Chun, A. Casparino, N. A. Patsopoulos et al., "Limited statistical evidence for shared genetic effects of eQTLs and autoimmune-disease-associated loci in three major immune-cell types", Nature Genetics (2017), Online Methods, "Joint likelihood mapping (JLIM)", <https://doi.org/10.1038/ng.3795> (PMC5374036).
