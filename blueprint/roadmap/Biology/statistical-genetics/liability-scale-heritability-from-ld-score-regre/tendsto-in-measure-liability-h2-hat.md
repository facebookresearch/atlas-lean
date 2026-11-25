# Consistency in probability of the liability-scale estimator

Let `ν` be a probability measure on `Ξ` and let `G` and `L` be real functions on `Ξ` (genetic value
and liability) such that the pair `(G, L)` has a Gaussian law under `ν` (`ν`-almost everywhere
measurable, with a possibly degenerate Gaussian law on `ℝ²`), with `L` measurable with the standard
normal law under `ν`; let `h²` be a real number with `Var G = h²` and `Cov(G, L) = h²` under `ν`,
let `t` be a real threshold and let `0 < P < 1`.

Let `μ` be a probability measure on `Ω` and `l` a filter on an index set `I`. For every `n ∈ I` let
`D_n` be an [LD-score model](../ld-score-regression/model.md) under `μ` with `N_n ≠ 0` individuals
and `M_n ≠ 0` markers, whose effects and noise terms have mean `0` under `μ` and whose heritability
equals the [case-control heritability proxy](case-control-h2-proxy.md) `h²_cc` of `G`, `L`, `t` and
`P` under `ν`; let `X_n` be a [standardized](../ld-score-regression/is-standardized.md) real
`N_n × M_n` genotype matrix whose [LD scores](../ld-score-regression/ld-score.md) are not all equal,
and let `s_n` be real and `c_n ∈ ℝ^{N_n}` be such that `s_n² (∑_i (X_n)_ij (c_n)_i / N_n)²` takes
the same value for every marker `j`. Let `ĥ²_n` be the
[unweighted estimator](../ld-score-regression/ols-h2-hat.md) and `ĥ²_{l,n}` the
[liability-scale estimator](liability-h2-hat.md), with threshold `t` and case fraction `P`, both
applied to the LD scores of `X_n` and the
[association statistics under stratification](../ld-score-regression/chi-sq-strat.md) of `D_n`,
`X_n`, `s_n` and `c_n`.

If the variance of `ĥ²_n` under `μ`, with values in `[0, ∞]`, tends to `0` along `l`, then
`ĥ²_{l,n}` converges to `h²` in `μ`-probability along `l`: for every `ε > 0`,
`μ(|ĥ²_{l,n} - h²| ≥ ε) → 0`.
