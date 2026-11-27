# Fixed-effects meta-analysis of correlated effect estimates

**Setting.** Let $\hat\beta = (\hat\beta_1, \dots, \hat\beta_T)^\top$ be estimates of one SNP's effect in $T$ datasets (for example $T$ tissues measured on overlapping sets of individuals) with known positive definite joint covariance $\Omega$, and suppose the fixed-effects model $\hat\beta \sim \mathcal{N}(\beta\mathbf{1}, \Omega)$ with a common effect $\beta$, where $\mathbf{1}$ is the vector of ones. In multi-tissue eQTL mapping $\hat\beta$ and $\Omega$ come from one generalized-least-squares fit of a linear mixed model with an individual random effect, so the per-tissue estimates are correlated.

**Estimator.**

$$\hat\beta_{\mathrm{FE}} = \frac{\mathbf{1}^\top \Omega^{-1}\hat\beta}{\mathbf{1}^\top \Omega^{-1}\mathbf{1}}, \qquad \operatorname{Var}(\hat\beta_{\mathrm{FE}}) = \frac{1}{\mathbf{1}^\top \Omega^{-1}\mathbf{1}},$$

and $\hat\beta_{\mathrm{FE}}/\sqrt{\operatorname{Var}(\hat\beta_{\mathrm{FE}})}$ is standard normal under $\beta = 0$. It is the best linear unbiased estimator of $\beta$ and the maximum-likelihood estimator under the Gaussian model. When $\Omega$ is diagonal it reduces to the average with the [inverse-variance weights](../../../../../../Probability/hypothesis-testing/meta-analysis/inverse-variance-weights.md) and its variance $(\sum_t \Omega_{tt}^{-1})^{-1}$.

## Remarks

This is generalized least squares for the one-parameter mean model $\mathbb{E}\hat\beta = \beta\mathbf{1}$: minimizing $(\hat\beta - b\mathbf{1})^\top\Omega^{-1}(\hat\beta - b\mathbf{1})$ gives $\hat\beta_{\mathrm{FE}}$, and its variance is $(\mathbf{1}^\top\Omega^{-1}\mathbf{1})^{-1}$; Gauss–Markov gives optimality among linear unbiased estimators. Ignoring positive correlation (treating $\Omega$ as diagonal) overstates the information in the data and inflates the test statistic. The source also builds working per-dataset variances $V_t = 1/(\Omega^{-1}\mathbf{1})_t$ from $\Omega$; fed to inverse-variance formulas for independent estimates, they reproduce $\hat\beta_{\mathrm{FE}}$ and its variance. This requires every row sum $(\Omega^{-1}\mathbf{1})_t$ to be positive, which positive definiteness does not guarantee: for the positive definite $\Omega$ with rows $(1, 1.5)$ and $(1.5, 4)$, $\Omega^{-1}\mathbf{1}$ is proportional to $(2.5, -0.5)$, and no positive variances reproduce these weights. Even when the row sums are positive, changing the reported variances does not make the estimates independent, so random-effects tests, heterogeneity statistics and $m$-values computed from the working variances are approximations, not the exact independent-study results.

## Depends on

- [Inverse-variance weights](../../../../../../Probability/hypothesis-testing/meta-analysis/inverse-variance-weights.md)

## Sources

- J. H. Sul, B. Han, C. Ye, T. Choi and E. Eskin, "Effectively identifying eQTLs from multiple tissues by combining mixed model and meta-analytic approaches", PLoS Genetics 9 (2013), e1003491, Materials and Methods (Equations (3), (4), (5) and (7), "Accounting for covariance of effect size estimates"), <https://doi.org/10.1371/journal.pgen.1003491>, PMCID PMC3681686.
