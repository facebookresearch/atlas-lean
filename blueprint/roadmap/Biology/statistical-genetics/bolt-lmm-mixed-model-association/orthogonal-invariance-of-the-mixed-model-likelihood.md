# Orthogonal invariance of the linear mixed model likelihood

**Model.** For $n$ individuals let $y \in \mathbb{R}^n$ be a phenotype vector, $X$ an $n \times p$ covariate matrix, and $H$ the $n \times m$ matrix of standardized genotypes, $H_{ij} = (G_{ij} - 2\pi_j)/\sqrt{2\pi_j(1 - \pi_j)}$. With genetic relationship matrix $K = \tfrac1m H H^\top$ and variance components $\sigma_g^2, \sigma_e^2 > 0$, the association model for SNP $j$ is

$$y = X\alpha + h_j \beta_j + e, \qquad \mathrm{Var}(e) = V = K\sigma_g^2 + I\sigma_e^2,$$

with $h_j$ the $j$-th column of $H$, and the Gaussian log-likelihood satisfies

$$-2 \log \ell(\alpha, \beta_j, \sigma_g^2, \sigma_e^2) = (y - X\alpha - h_j\beta_j)^\top V^{-1} (y - X\alpha - h_j\beta_j) + \log\lvert V \rvert + n \log(2\pi).$$

**Theorem.** Let $P$ be any $n \times n$ orthogonal matrix ($P^\top P = I$) and transform the data to $z = Py$, $W = PX$, $F = PH$. Then

1. $F^\top F = H^\top H$, so SNP–SNP correlations (linkage disequilibrium) are unchanged, while the relationship matrix becomes $\tfrac1m F F^\top = P K P^\top$;
2. $\mathrm{Var}(z) = P V P^\top = (P K P^\top)\sigma_g^2 + I \sigma_e^2$, so $z$ follows the same mixed model with the same $\sigma_g^2$, $\sigma_e^2$ and heritability $h^2 = \sigma_g^2/(\sigma_g^2 + \sigma_e^2)$;
3. the log-likelihood of $(z, W, F)$ under the transformed model equals that of $(y, X, H)$ at every parameter value.

Hence maximum-likelihood and REML estimates, likelihood-ratio and Wald tests and their p-values are identical on the transformed data. The same holds for ridge regression, LASSO and Henderson's mixed-model equations.

## Proof sketch

Item 1 is $F^\top F = H^\top P^\top P H$. For item 3, the residual transforms as $z - W\alpha - f_j\beta_j = P(y - X\alpha - h_j\beta_j)$ and $(P V P^\top)^{-1} = P V^{-1} P^\top$, so the quadratic form is unchanged; $\lvert P V P^\top \rvert = \lvert P \rvert^2 \lvert V \rvert = \lvert V \rvert$ because $\lvert P \rvert = \pm 1$. With $A = V^{1/2}$, the decorrelating map $B = PAP^\top$ (for example) satisfies $\mathrm{Var}(B^{-1} z) = I$, so the transformed model reduces to ordinary least squares exactly as the original does. For ridge regression, $((PX)^\top PX + \lambda I)^{-1} (PX)^\top Py = (X^\top X + \lambda I)^{-1} X^\top y$. Geometrically, standardized SNP and phenotype columns are points on a sphere in $\mathbb{R}^n$ and associations are angles between them, which rotations preserve. A random orthogonal $P$ therefore acts as an encryption key: the rows of the transformed data no longer correspond to individuals, yet every likelihood-based quantitative-genetic analysis can be run on them unchanged.

## Depends on

- [Marginal log-likelihood of the mean](log-lik.md)
- [Marginal phenotypic covariance matrix](v.md)

## Sources

- R. Mott, C. Fischer, P. Prins et al., "Private genomes and public SNPs: homomorphic encryption of genotypes and phenotypes for shared quantitative genetics", Genetics (2020), <https://doi.org/10.1534/genetics.120.303153>, PMCID PMC7268998. Sections "Statistical preliminaries" and "Orthogonal transformations", Equations 1–16.
