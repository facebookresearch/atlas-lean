# Population consistency on the liability scale

Let `ν` be a probability measure on `Ξ` and let `G` and `L` be real functions on `Ξ` (genetic value
and liability) such that the pair `(G, L)` has a Gaussian law under `ν` (`ν`-almost everywhere
measurable, with a possibly degenerate Gaussian law on `ℝ²`), with `L` measurable with the standard
normal law under `ν`; let `h²` be a real number with `Var G = h²` and `Cov(G, L) = h²` under `ν`,
let `t` be a real threshold and let `0 < P < 1`.

Let `μ` be a probability measure on `Ω` and let `D` be an
[LD-score model](../ld-score-regression/model.md) under `μ` with `N ≠ 0` individuals and `M ≠ 0`
markers, whose effects `β_k` and noise terms `ε_i` have mean `0` under `μ`, and whose heritability
equals the [case-control heritability proxy](case-control-h2-proxy.md) `h²_cc` of `G`, `L`, `t` and
`P` under `ν`. Let `X` be a [standardized](../ld-score-regression/is-standardized.md) real `N × M`
genotype matrix whose [LD scores](../ld-score-regression/ld-score.md) `ℓ_j` are not all equal, and
let `s` be real and `c ∈ ℝ^N` be such that the confounding term `s² (∑_i X_ij c_i / N)²` takes the
same value for every marker `j`. Write `χ²_j` for the
[association statistics under stratification](../ld-score-regression/chi-sq-strat.md) of `D`, `X`,
`s` and `c`, and `ĥ²_l(χ)` for the [liability-scale estimator](liability-h2-hat.md) with threshold
`t`, case fraction `P`, `N`, `M`, the LD scores `ℓ` and statistics `χ`.

Then the estimator applied to the expected statistics returns the liability-scale heritability:

`ĥ²_l((E χ²_j)_j) = h²`.

The step from binary case-control statistics to this regression model, with its heritability equal
to the case-control proxy, is a hypothesis, not derived.
