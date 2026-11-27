# Independence of location and scale tests and the joint location-scale statistic

**Setting.** Observations $Y_i \sim N(\beta_0 + \beta_1 x_i, \sigma_{x_i}^2)$, $i = 1,\dots,n$, independent, with genotype $x_i \in \{0,1,2\}$. The **location statistic** is the regression $t$-statistic

$$T_{\mathrm{L}} = \frac{\hat\beta_1}{S/\sqrt{S_{xx}}}, \quad \hat\beta_1 = \frac{S_{xy}}{S_{xx}},\quad S^2 = \frac{1}{n-2}\sum_i(y_i - \hat\beta_0 - \hat\beta_1x_i)^2,$$

and the **scale statistic** $T_{\mathrm{S}}$ is Levene's statistic for equality of the three genotype-group variances.

**Lemma.** If $\sigma_0^2 = \sigma_1^2 = \sigma_2^2$, then $T_{\mathrm L}$ and $T_{\mathrm S}$ are independent.

**Joint test.** Test $H_0^{\mathrm{joint}}: \beta_1 = 0$ and $\sigma_0 = \sigma_1 = \sigma_2$ against $H_1^{\mathrm{joint}}: \beta_1 \ne 0$ or some $\sigma_i \ne \sigma_j$. With $p_{\mathrm L}, p_{\mathrm S}$ the $p$-values of the location and scale tests,

$$W_F = -2\big(\log p_{\mathrm L} + \log p_{\mathrm S}\big) \sim \chi^2_4, \qquad W_M = \min(p_{\mathrm L},p_{\mathrm S}) \sim \mathrm{Beta}(1,2) \quad \text{under } H_0^{\mathrm{joint}}.$$

For a gene set of $J$ SNPs, $\sum_j W_{F,j}$ is referred to its phenotype-permutation distribution, which accounts for linkage disequilibrium.

## Depends on

- [Chi-square distribution](../../../../../../Probability/distributions/continuous/chi-square-distribution/chi-square-measure.md)

## Proof depends on

- [Ancillary statistic](../../../../../../Probability/statistical-estimation/completeness-ancillarity-and-the-lehmann-scheff/is-ancillary.md)
- [Complete statistic](../../../../../../Probability/statistical-estimation/completeness-ancillarity-and-the-lehmann-scheff/is-complete-statistic.md)
- [Fisher's method for combining p-values](../../../../../../Probability/hypothesis-testing/meta-analysis/has-law-fisher-statistic.md)

## Related topics

- [Genotype-dependent trait variance from unmodelled interaction](genotype-dependent-trait-variance-from-unmodelled-interaction.md): why a genotype-dependent variance signals interaction with an unmeasured factor.

## Expansion

Under the homoscedastic null the model is a full-rank exponential family in $\theta = (\beta_1/\sigma^2, -1/(2\sigma^2), \beta_0/\sigma^2)$ with complete sufficient statistic $(\sum x_iy_i, \sum y_i^2, \sum y_i)$. Levene's statistic is built from within-group absolute deviations and is invariant to shifts within groups and to a common rescaling, so its distribution does not depend on $\theta$: it is ancillary. Basu's theorem makes it independent of the sufficient statistic, and $T_{\mathrm L}$ is a function of that statistic. Independent uniform $p$-values give $-2\log p \sim \chi^2_2$ each, hence $W_F \sim \chi^2_4$, and $\Pr(\min(p_{\mathrm L},p_{\mathrm S}) \le w) = 1-(1-w)^2$, the $\mathrm{Beta}(1,2)$ law. The same argument applies with an ANOVA $F$ location test.

## Sources

- D. Soave, H. Corvol, N. Panjwani, J. Gong, W. Li, P.-Y. Boëlle, P. R. Durie, A. D. Paterson, J. M. Rommens, L. J. Strug, L. Sun, "A joint location-scale test improves power to detect associated SNPs, gene sets, and pathways", American Journal of Human Genetics 97(1) (2015) 125–138, Material and Methods (joint location-scale testing for single-SNP and gene-set analysis) and Appendix A, Lemma 1, <https://doi.org/10.1016/j.ajhg.2015.05.015>, PMCID PMC4572492.
