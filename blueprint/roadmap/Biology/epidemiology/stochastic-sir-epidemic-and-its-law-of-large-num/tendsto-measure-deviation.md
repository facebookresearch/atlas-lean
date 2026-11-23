# Kurtz's law of large numbers for the stochastic SIR epidemic

**Kurtz's law of large numbers for the stochastic SIR epidemic** (Kurtz 1970, Thm 3.1;
Ethier–Kurtz 1986, ch. 11, Thm 2.1, SIR instance). For each population size `N` let
`(S N, I N, R N)` be the SIR chain driven by unit-rate Poisson processes `Y₁ N` (infection) and
`Y₂ N` (recovery), i.e. almost every sample path solves the random time-change equations of
`IsChainPath` with infection rate `β S I / N` and recovery rate `γ I`. Let `(s, i, r)` solve the
SIR system `s' = -β s i`, `i' = β s i - γ i`, `r' = γ i` from a point of the simplex. If the
scaled initial state converges to `(s 0, i 0, r 0)` in probability, then the scaled chain
converges to `(s, i, r)` in probability, uniformly on every time interval `[0, T]`: the
probability that the deviation reaches `ε` at some time of `[0, T]` tends to `0`,

`P(∃ t ∈ [0, T], |S/N - s| + |I/N - i| + |R/N - r| ≥ ε) → 0`  as `N → ∞`.

This event contains the strict supremum event `sup_{t ∈ [0, T]} deviation > ε`. A supremum need
not be attained, so the non-strict supremum event `sup deviation ≥ ε` is the separate corollary
`tendsto_measure_iSup_deviation`. The event is not assumed measurable; `μ` is applied as an outer
measure.
