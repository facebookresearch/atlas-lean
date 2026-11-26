# lassosum: the LASSO from summary statistics with a shrunk reference LD matrix

For a linear model $y = X\beta + \epsilon$ with $X$ an $n \times p$ matrix, the LASSO minimizes

$$f(\beta) = (y - X\beta)^\top (y - X\beta) + 2\lambda \lVert \beta \rVert_1 = y^\top y + \beta^\top X^\top X \beta - 2\beta^\top X^\top y + 2\lambda \lVert \beta \rVert_1, \qquad \lambda \ge 0.$$

If $X$ and $y$ are standardized and divided by $\sqrt n$, then $R = X^\top X$ is the SNP correlation (LD) matrix and $r = X^\top y$ the vector of marginal SNP–trait correlations, so $f(\beta) = y^\top y + \beta^\top R \beta - 2\beta^\top r + 2\lambda\lVert\beta\rVert_1$ depends on the data only through $(R, r)$.

When $R$ is replaced by an estimate $X_r^\top X_r$ from a reference panel $X_r$ different from the GWAS sample, the quadratic part need not be bounded below on the directions where $r$ is not in the range of $X_r^\top X_r$. **lassosum** instead uses, for $0 < s < 1$,

$$R_s = (1 - s) X_r^\top X_r + s I, \qquad f_s(\beta) = y^\top y + \beta^\top R_s \beta - 2\beta^\top r + 2\lambda \lVert\beta\rVert_1.$$

Then:

1. $R_s$ is positive definite, and minimizing $f_s$ is a LASSO problem: there are $W$, $v$ with $W^\top W = R_s$ and $W^\top v = r$, and $f_s(\beta) = \lVert v - W\beta \rVert^2 + 2\lambda\lVert\beta\rVert_1 + \text{const}$.
2. Expanding, $f_s(\beta) = y^\top y + (1 - s)\beta^\top X_r^\top X_r \beta - 2\beta^\top r + s\, \beta^\top\beta + 2\lambda \lVert\beta\rVert_1$, an elastic-net objective with ridge weight $s$ and LASSO weight $\lambda$ on the reference-panel least-squares problem.

The polygenic score weights are the minimizer $\hat\beta(\lambda, s)$; it is unique because $f_s$ is strictly convex.

## Expansion

Take $W = R_s^{1/2}$ and $v = R_s^{-1/2} r$; then $\lVert v - W\beta\rVert^2 = v^\top v - 2\beta^\top r + \beta^\top R_s \beta$, which differs from $f_s - 2\lambda\lVert\beta\rVert_1$ by a constant. Positive definiteness of $R_s$ follows because $X_r^\top X_r \succeq 0$ and $s > 0$; strict convexity of the quadratic gives uniqueness.

## Sources

- T. S. H. Mak, R. M. Porsch, S. W. Choi, X. Zhou and P. C. Sham, "Polygenic scores via penalized regression on summary statistics", *Genetic Epidemiology* 41 (2017), 469–480, <https://doi.org/10.1002/gepi.22050>. Equations (1)–(8) and the accompanying proof, as numbered in the preprint version that was read.
