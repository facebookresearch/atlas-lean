# Invariance of GLM association tests under block-triangular reparametrization of the design

Let $Y$ be an $n$-vector of responses following a generalized linear model $g(E[Y]) = X\beta$ with a fixed link $g$. Consider two full-column-rank $n \times p$ design matrices split into $p - q$ secondary columns (not tested, including any intercept) and $q$ primary columns (tested),

$$X_1 = (X_{11}, X_{12}), \qquad X_2 = (X_{21}, X_{22}),$$

with null hypotheses $H_0^{(1)} : \beta_{12} = 0$ and $H_0^{(2)} : \beta_{22} = 0$ on the primary coefficients.

**Theorem.** Suppose there is an invertible block upper-triangular matrix

$$T = \begin{pmatrix} T_{11} & T_{12} \\ 0 & T_{22} \end{pmatrix}, \qquad T_{11} \in \mathbb{R}^{(p-q)\times(p-q)},\ T_{22} \in \mathbb{R}^{q \times q},$$

with $X_2 = X_1 T$, i.e. $X_{21} = X_{11}T_{11}$ and $X_{22} = X_{11}T_{12} + X_{12}T_{22}$. Then the likelihood-ratio, Wald and score statistics for $H_0^{(1)}$ under $X_1$ coincide with those for $H_0^{(2)}$ under $X_2$.

The primary columns need not be linear transformations of each other: $X_{22}$ may differ from $X_{12}T_{22}$ by any combination of the secondary columns.

## Expansion

Because $T$ is invertible, $X_1$ and $X_2$ span the same column space, so the two parametrizations describe the same family of mean vectors, $\beta^{(2)} = T^{-1}\beta^{(1)}$, and the maximized full likelihoods agree. Block upper-triangularity gives $\beta^{(2)}_{22} = T_{22}^{-1}\beta^{(1)}_{12}$, so the two null hypotheses define the same submodel, spanned by $X_{11}$ and $X_{21} = X_{11}T_{11}$; the maximized null likelihoods also agree and the LRT is identical. The Wald statistic is invariant because $\hat\beta_{22} = T_{22}^{-1}\hat\beta_{12}$ and its estimated covariance transforms by the same congruence, and the score statistic is invariant because the score and information at the common null fit transform by $T^\top$ and $T^\top(\cdot)T$. The familiar case in which the primary columns are affine images of each other (e.g. switching the coded allele of an autosomal SNP, $X_{22} = \mathbf{1} - X_{12}$) is the special case with $T_{12}$ nonzero only in its intercept row.

## Sources

- B. Chen, R. V. Craiu, L. J. Strug and L. Sun, "The X factor: A robust and powerful approach to X-chromosome-inclusive whole-genome association studies", Genetic Epidemiology 45 (2021), 694, <https://doi.org/10.1002/gepi.22422> (PMC9292551). Section 2, Theorem 1 (proof in Supporting Information Appendix A).
