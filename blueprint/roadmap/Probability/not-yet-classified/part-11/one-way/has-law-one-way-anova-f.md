# One-way ANOVA `F` test

Under `H₀` with `G ≥ 2` groups and `n > G`, the standardized
ratio `((SSB / v) / (G - 1)) / ((SSW / v) / (n - G)) ~ F(G - 1, n - G)`. For the observable
statistic without the unknown variance `v`, use `hasLaw_oneWay_ANOVA_F_varianceFree`.
