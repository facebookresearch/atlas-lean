# Kurtz's law of large numbers for density-dependent stochastic reaction networks

(Kurtz 1970, Thm 3.1; Ethier–Kurtz 1986, ch. 11, Thm 2.1). Let `C N` be stochastic reaction
networks on the reaction network `G`, indexed by the system size `N`, and `β_r` locally Lipschitz
macroscopic rate functions such that the scaled propensities converge uniformly on bounded sets,

`sup_{‖z / N‖ ≤ R} |λ^N_r(z) / N - β_r(z / N)| → 0`  for every `R`.

For each `N` let `X N` be the chain driven by unit-rate Poisson processes `Y N r`, i.e. almost
every sample path solves the random time-change equations of `IsChainPath`. Let `x` solve the
mean-field equation `x' = ∑_r β_r(x) ζ_r`. If the scaled initial state converges to `x(0)` in
probability, then the scaled chain converges to `x` in probability, uniformly on every `[0, T]`:

`P(∃ t ∈ [0, T], ‖X^N(t) / N - x(t)‖₁ ≥ ε) → 0`  as `N → ∞`.

The event is not assumed measurable; `μ` is applied as an outer measure.
