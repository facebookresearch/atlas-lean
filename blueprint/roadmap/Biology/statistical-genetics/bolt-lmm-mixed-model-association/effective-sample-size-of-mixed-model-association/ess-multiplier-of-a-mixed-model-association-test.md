# Effective sample size multiplier of a mixed-model association test

Let $y \in \mathbb{R}^N$ be a standardized quantitative trait and $w \in \mathbb{R}^N$ a standardized genotype vector, with model $y \sim \mathcal{N}(w\beta, \Sigma_y)$ and known positive definite trait covariance $\Sigma_y$ (in practice $\Sigma_y = \sum_k \sigma_k^2 R_k + \sigma_r^2 I$ with variance components estimated by REML). The generalized least squares (LMM) estimator and Wald statistic are

$$\hat\beta_{\mathrm{LMM}} = \frac{w^\top \Sigma_y^{-1} y}{w^\top \Sigma_y^{-1} w}, \qquad \operatorname{var}(\hat\beta_{\mathrm{LMM}}) = \frac{1}{w^\top \Sigma_y^{-1} w}, \qquad s_{\mathrm{LMM}} = \frac{(w^\top \Sigma_y^{-1} y)^2}{w^\top \Sigma_y^{-1} w},$$

while linear regression on unrelated individuals has $\operatorname{var}(\hat\beta_{\mathrm{LR}}) \approx 1/N$. Under the alternative the noncentrality parameter of the $\chi^2_1$ statistic is $\mathrm{NCP}_\beta = \beta^2 / \operatorname{var}(\hat\beta)$, and power is $1 - F(\chi^2_{1,1-\alpha} \mid 1, \mathrm{NCP}_\beta)$. The **ESS multiplier** is

$$\gamma_\beta = \frac{\mathrm{NCP}_{\beta,\mathrm{LMM}}}{\mathrm{NCP}_{\beta,\mathrm{LR}}} \approx \frac{w^\top \Sigma_y^{-1} w}{N}, \qquad \mathrm{ESS} = N\gamma_\beta .$$

**Trace approximation.** If $w$ is a random vector with mean $0$ and covariance $\Sigma_w$ (identity for unrelated individuals, the kinship matrix $K$ for pedigrees), then $\mathbb{E}[w^\top A w] = \operatorname{tr}(A \Sigma_w)$, so

$$\gamma_\beta \approx \frac{\operatorname{tr}(\Sigma_y^{-1} \Sigma_w)}{N}.$$

For $\Sigma_y = \sigma_g^2 G + \sigma_r^2 I$ with symmetric $G$ having eigenvalues $\lambda_1, \dots, \lambda_N$ and unrelated individuals ($\Sigma_w = I$), this is $\gamma_\beta \approx N^{-1} \sum_i (\sigma_g^2 \lambda_i + \sigma_r^2)^{-1}$; for families with $\Sigma_y = \sigma_a^2 K + \sigma_r^2 I$ and $\Sigma_w = K$, it is $\gamma_\beta \approx N^{-1}\sum_i (\sigma_a^2 + \sigma_r^2 / \lambda_i^K)^{-1}$.

## Depends on

- [Generalized least-squares matrix](../../../../Probability/linear-models-multivariate/generalized-least-squares/gls-matrix.md): with a single regressor $w$
- [Mixed-model association chi-squared statistic](../../proximal-contamination-in-mixed-model-associatio/mm-chi-sq.md): the statistic $s_{\mathrm{LMM}}$
- [Ordinary least-squares estimator](../../../../Probability/linear-models-multivariate/ordinary-least-squares/sampling-properties-of-the-ordinary-least-square/ols-estimator.md): the linear-regression comparison
- [Chi-square distribution](../../../../Probability/distributions/continuous/chi-square-distribution/chi-square-measure.md)

## Proof depends on

- [Local power of the likelihood-ratio test](../../../../Probability/hypothesis-testing/local-power-of-the-likelihood-ratio-test/tendsto-in-distribution-two-mul-log-like-2.md): the noncentral $\chi^2_1$ law of the statistic under the alternative

## Expansion

The LMM statistic is the GLS Wald test, so its NCP is $\beta^2 w^\top \Sigma_y^{-1} w$, and the ratio to the regression NCP $\beta^2 N$ gives $\gamma_\beta$. For a random vector $X$ with mean $\mu$ and covariance $\Sigma$, $\mathbb{E}[X^\top A X] = \operatorname{tr}(A\Sigma) + \mu^\top A \mu$; with $\mu = 0$ only the trace remains. Diagonalizing $G$ (or $K$) simultaneously diagonalizes $\Sigma_y$, which turns the trace into the eigenvalue sums. A gene–environment interaction test is handled identically with $v = w \circ d$ in place of $w$ and $\Sigma_v = D \circ \Sigma_w$, $D_{ij} = d_i d_j$, giving $\gamma_\delta \approx \operatorname{tr}(\Sigma_y^{-1}(D \circ \Sigma_w))/N$. When modelling relatedness as a random effect removes trait variance from the residual, $\gamma_\beta > 1$ and the LMM behaves like a larger unrelated sample; the empirical analogue is the median ratio of squared standard errors $\operatorname{var}(\hat\beta_{\mathrm{LR}})/\operatorname{var}(\hat\beta_{\mathrm{LMM}})$ over random variants.

## Sources

- A. Ziyatdinov, J. Kim, D. Prokopenko, F. Privé, F. Laporte, P.-R. Loh, P. Kraft and H. Aschard, "Estimating the effective sample size in association studies of quantitative traits", *G3: Genes, Genomes, Genetics* (2021), jkab057, Methods Eqs. (1)–(4), (15)–(17), (22)–(25) and Results Eqs. (26)–(30), <https://doi.org/10.1093/g3journal/jkab057> (PMC8495748).
