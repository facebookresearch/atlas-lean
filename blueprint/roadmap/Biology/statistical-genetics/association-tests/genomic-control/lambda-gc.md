# Population genomic-control factor of the LD-score model

Consider an [LD-score model](../../ld-score-regression/model.md) on a measure `μ`, with `N`
individuals and `M` markers, a real `N × M` genotype matrix `X`, a real number `s` and a
stratification axis `c ∈ ℝ^N`. The population genomic-control factor is the average over the
markers of the integrals of the
[association statistics under stratification](../../ld-score-regression/chi-sq-strat.md) `χ²_j`:

`λ_GC = (1 / M) ∑_j ∫ χ²_j dμ`.

When `μ` is a probability measure, as in the results that use it, this is the mean expected
association statistic `(1 / M) ∑_j 𝔼[χ²_j]`, the population version of the mean-based estimator
of the inflation factor `λ`. The formula is defined for every measure, with the integral of a
non-integrable function taken to be `0`; with the convention `x / 0 = 0` it is `0` when `M = 0`.
