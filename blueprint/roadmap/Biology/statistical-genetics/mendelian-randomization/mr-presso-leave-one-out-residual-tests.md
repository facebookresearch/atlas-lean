# MR-PRESSO: leave-one-out residual tests for horizontal pleiotropy

Let variants $j = 1, \dots, n$ have estimated effects $\gamma_j$ on the exposure and $\Gamma_j$ on the outcome, with sampling variances $\mathbb V(\gamma_j)$ and $\mathbb V(\Gamma_j)$. For each $j$, let $\hat\beta_{-j}$ be the causal slope of the regression of $\Gamma$ on $\gamma$ fitted to all variants except $j$.

**Global test.** The observed statistic is the leave-one-out residual sum of squares

$$\mathrm{RSS}_{\mathrm{obs}} = \sum_{j=1}^n \mathrm{RSS}_{\mathrm{obs}}(j), \qquad \mathrm{RSS}_{\mathrm{obs}}(j) = \bigl(\Gamma_j - \hat\beta_{-j}\gamma_j\bigr)^2 .$$

Its null distribution is simulated: draw $\Gamma_j^{\mathrm{random}} \sim \mathcal N(\hat\beta_{-j}\gamma_j, \mathbb V(\Gamma_j))$ and $\gamma_j^{\mathrm{random}} \sim \mathcal N(\gamma_j, \mathbb V(\gamma_j))$ independently, and set

$$\mathrm{RSS}_{\mathrm{exp}} = \sum_{j=1}^n \bigl(\Gamma_j^{\mathrm{random}} - \hat\beta_{-j}\gamma_j^{\mathrm{random}}\bigr)^2 .$$

Repeating this $K$ times, the empirical $P$-value is the fraction of draws with $\mathrm{RSS}_{\mathrm{exp}} > \mathrm{RSS}_{\mathrm{obs}}$.

**Outlier test.** For each variant, compare $\mathrm{RSS}_{\mathrm{obs}}(j)$ with its $K$ simulated values $\mathrm{RSS}_{\mathrm{exp}}(j)$ to get a per-variant empirical $P$-value. Then Bonferroni-correct over the $n$ variants, and remove the variants declared outliers.

**Distortion test.** With $\hat\beta_{\mathrm{raw}}$ the causal estimate from all variants and $\hat\beta_{\mathrm{corr}}$ the estimate after removing the $n_o$ outliers,

$$D = 100 \times \frac{\hat\beta_{\mathrm{raw}} - \hat\beta_{\mathrm{corr}}}{\lvert \hat\beta_{\mathrm{corr}} \rvert}.$$

Its null is built by keeping the $n_o$ outliers and replacing the non-outlier set with $n - 2n_o$ variants resampled with replacement from the non-outliers. This keeps $n - n_o$ variants, and the estimate is recomputed 10,000 times.

## Depends on

- [Inverse-variance-weighted estimator](ivw.md)
- [Directional pleiotropy biases the IVW estimator](ivw-of-pleiotropy.md)

## Expansion

Without pleiotropy, $\Gamma_j = \beta\gamma_j$ up to sampling noise, so each held-out residual has the spread implied by the standard errors alone, which is exactly what the simulated null draws. A variant with a direct effect $\alpha_j \ne 0$ inflates its own residual by about $\alpha_j^2$. Leaving it out of $\hat\beta_{-j}$ keeps it from pulling the line towards itself. The global test is thus a parametric-bootstrap analogue of Cochran's $Q$ for heterogeneity of ratio estimates.

## Sources

- M. Verbanck, C.-Y. Chen, B. Neale and R. Do, *Detection of widespread horizontal pleiotropy in causal relationships inferred from Mendelian randomization between complex traits and diseases*, Nat. Genet. 50 (2018), 693–698, <https://doi.org/10.1038/s41588-018-0099-7>, PMCID PMC6083837 (Online Methods, "MR-PRESSO": the global, outlier and distortion tests, as read from the authors' preprint version of the same methods).
