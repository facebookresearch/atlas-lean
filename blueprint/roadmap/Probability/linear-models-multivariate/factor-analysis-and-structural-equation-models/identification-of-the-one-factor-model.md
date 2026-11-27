# Identification of a one-factor model from three indicators

Let $X_j=\lambda_j F+\varepsilon_j$ for a finite collection of indicators. Assume that $F$ and the errors $\varepsilon_j$ are square-integrable, that $\operatorname{Var}(F)=1$, and that the errors are pairwise uncorrelated and uncorrelated with $F$. Write $\omega_j=\operatorname{Var}(\varepsilon_j)$ and let $\Sigma$ be the covariance matrix of the observations. Then $\Sigma=\lambda\lambda^{\mathsf T}+\operatorname{diag}(\omega)$, so $\sigma_{jk}=\lambda_j\lambda_k$ for $j\ne k$.

If there are at least three indicators and every loading is nonzero, then for any distinct $i,j,k$,

$$\lambda_i^2=\frac{\sigma_{ij}\sigma_{ik}}{\sigma_{jk}},\qquad \omega_i=\sigma_{ii}-\lambda_i^2.$$

Under these same assumptions, any other one-factor parameters with the same covariance have the same error variances and either the same loadings or their common negation. Fixing the sign of any one loading removes this ambiguity. Neither Gaussianity nor independence is needed for this covariance result.

The [three-indicator counterexample](one-factor-zero-loading-counterexample.md) shows that a zero loading can break identification.

## Sources

- J. Brunner, *Confirmatory factor analysis, part 1*, STA 431 lecture slides, University of Toronto, 2023, slides 3–4 and 13, <https://utstat.utoronto.ca/brunner/oldclass/431s23/lectures/431s23CFA1.pdf>.
