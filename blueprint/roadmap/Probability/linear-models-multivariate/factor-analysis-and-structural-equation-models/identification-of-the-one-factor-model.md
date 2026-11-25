# Identification of a one-factor model from three indicators

Let $X_j = \lambda_j F + \varepsilon_j$ for $j = 1, \dots, p$ with $p \ge 3$, square-integrable $F$ and $\varepsilon_j$, $\operatorname{Var}(F) = 1$, all $\lambda_j \ne 0$, and errors uncorrelated with each other and with $F$, with variances $\omega_j \ge 0$. Then $\sigma_{jk} = \lambda_j\lambda_k$ for $j \ne k$, so $\lambda_1^2 = \sigma_{12}\sigma_{13}/\sigma_{23}$ and similarly for each loading using any two other indicators; the loadings are determined up to one common sign, fixed by declaring the sign of one loading, and then $\omega_j = \sigma_{jj} - \lambda_j^2$. A zero loading can break this: with $p = 3$, loadings $(0, 1, 1)$ with error variances $(1, 4, 1)$ and loadings $(0, 2, \tfrac12)$ with error variances $(1, 1, \tfrac74)$ give the same covariance matrix.

## Sources

- J. Brunner, *Confirmatory factor analysis, part 1*, STA 431 lecture slides, University of Toronto, 2023, slides 3–4 and 13, <http://utstat.utoronto.ca/brunner/oldclass/431s23/lectures/431s23CFA1.pdf>
