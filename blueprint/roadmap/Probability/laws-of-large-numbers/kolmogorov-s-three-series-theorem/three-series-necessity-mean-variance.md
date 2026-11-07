# Kolmogorov three-series necessity, series (2)–(3)

If the partial
sums of an independent sequence `Xₙ` converge almost surely, then for
every `A > 0` the truncations `Yₙ = Xₙ · 1_{|Xₙ| ≤ A}` have convergent
mean partial sums and summable variances. This is the corrected form of
v1's `summable_mean_and_variance_of_ae_tendsto_ax`: v1 claimed the means
themselves are `Summable`, which is false (see
`summable_mean_necessity_false`); only convergence of the mean partial
sums holds. Series (1) uses the public theorem from
`ThreeSeriesTailProb`.
