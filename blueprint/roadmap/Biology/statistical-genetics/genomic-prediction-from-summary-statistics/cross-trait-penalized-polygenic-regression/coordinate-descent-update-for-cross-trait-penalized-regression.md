# Coordinate-descent update for cross-trait penalized regression

Consider the [cross-trait Laplacian-penalized least squares](cross-trait-laplacian-penalized-least-squares.md) objective with the data standardized so that, for every trait $k$ and SNP $j$, $\sum_i x_{kij}^2 = n_k$, $\sum_i x_{kij} = 0$ and $\sum_i y_{ki} = 0$ (so the intercepts drop out). Fix all coefficients except $\beta_{k'j'}$ at current values $\tilde\beta$, and define the partial residuals and the summaries

$$\tilde r_{k'ij'} = y_{k'i}-\sum_{j\ne j'}x_{k'ij}\tilde\beta_{k'j},\qquad \tilde\zeta_{k'j'} = \frac{1}{n_{k'}}\sum_{i=1}^{n_{k'}}x_{k'ij'}\tilde r_{k'ij'},$$

$$\tilde\xi_{k'j'} = \lambda_2\Big(\sum_{k\ne k'}a_{kk'j'}\tilde\beta_{kj'}+\sum_{m=1}^{M}a_{k'(K+m)j'}\hat s_{mj'}\Big),\qquad d_{k'j'} = \sum_{k\ne k'}a_{kk'j'}+\sum_{m=1}^{M}a_{k'(K+m)j'},$$

and $\tilde b_{k'j'} = \tilde\zeta_{k'j'}+\tilde\xi_{k'j'}$.

**Proposition.** The objective restricted to $\beta_{k'j'}$ equals, up to a constant,

$$\tfrac12\big(\beta_{k'j'}-\tilde b_{k'j'}\big)^2 + p^{\mathrm{sp}}(\beta_{k'j'}) + \tfrac{\lambda_2}{2}\,d_{k'j'}\,\beta_{k'j'}^2,$$

and its minimizer is, for the Lasso,

$$\hat\beta_{k'j'} = \frac{\operatorname{sgn}(\tilde b_{k'j'})\,\big(|\tilde b_{k'j'}|-\lambda_1\big)_+}{1+\lambda_2 d_{k'j'}},$$

and for the MCP with $\gamma(1+\lambda_2 d_{k'j'}) > 1$,

$$\hat\beta_{k'j'} = \begin{cases}\dfrac{\operatorname{sgn}(\tilde b_{k'j'})\,\gamma\,\big(|\tilde b_{k'j'}|-\lambda_1\big)_+}{\gamma(1+\lambda_2 d_{k'j'})-1}, & |\tilde b_{k'j'}|\le \gamma\lambda_1(1+\lambda_2 d_{k'j'}),\\[2ex] \dfrac{\tilde b_{k'j'}}{1+\lambda_2 d_{k'j'}}, & |\tilde b_{k'j'}| > \gamma\lambda_1(1+\lambda_2 d_{k'j'}).\end{cases}$$

As $\gamma\to\infty$ the MCP update tends to the Lasso update.

## Depends on

- [Cross-trait Laplacian-penalized least squares](cross-trait-laplacian-penalized-least-squares.md): the objective being minimized
- [Standardized genotype matrix](../../ld-score-regression/is-standardized.md): the standardization $\sum_i x_{kij} = 0$, $\sum_i x_{kij}^2 = n_k$
- [Soft thresholding](../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/soft-threshold.md): the operator $\operatorname{sgn}(b)(|b|-\lambda_1)_+$ in both updates

## Proof depends on

- [Soft thresholding solves the one-dimensional lasso](../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/soft-threshold-le.md): the Lasso minimizer of the univariate problem

## Expansion

With standardized genotypes the least-squares part restricted to one coordinate is $\frac12\beta^2 - \tilde\zeta\beta$ plus a constant, and the Laplacian part contributes $\frac{\lambda_2}{2}d\beta^2 - \tilde\xi\beta$ plus a constant; completing the square in $\beta$ for the linear terms gives the stated univariate problem. Its stationarity condition is $(1+\lambda_2 d)\beta = \tilde b - \partial p^{\mathrm{sp}}(\beta)$, whose solution is soft-thresholding at $\lambda_1$ followed by division by $1+\lambda_2 d$ for the Lasso; for the MCP the penalty derivative $\lambda_1(1-|\beta|/(\gamma\lambda_1))_+$ vanishes beyond $\gamma\lambda_1$, giving the unpenalized ridge-type value there and a firm-thresholding rule below. Cycling the update over all traits and SNPs, maintaining residuals incrementally, iterating on the active set and using warm starts along a decreasing $\lambda_1$ path from $\lambda_1^{\max} = \max_{k,j}|\sum_i x_{kij}y_{ki}|/n_k$ (the smallest value giving $\hat\beta = 0$ when no summary-statistic anchors are used) yields an $O(NP)$ cost per sweep, where $N = \sum_k n_k$.

## Sources

- W. Chung, J. Chen, C. Turman, S. Lindstrom, Z. Zhu, P.-R. Loh, P. Kraft and L. Liang, "Efficient cross-trait penalized regression increases prediction accuracy in large cohorts using secondary phenotypes", Nature Communications 10 (2019), Methods, "Coordinate descent algorithm", Eqs. (4)–(6), <https://doi.org/10.1038/s41467-019-08535-0>, PMCID PMC6361917.
