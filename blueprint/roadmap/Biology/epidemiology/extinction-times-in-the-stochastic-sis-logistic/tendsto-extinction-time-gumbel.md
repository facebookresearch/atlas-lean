# Gumbel limit of the extinction time

Brightwell, House and Luczak (2018), Theorem 1.1 and
Eq. (1.4): let `λ(N)` and `μ(N)` be bounded away from `0` and `∞`, with `(μ - λ) √N → ∞`, and
let the initial states `x₀(N) ∈ {0, …, N}` be deterministic with `x₀(N) (μ - λ) → ∞`. Then for
every real `w`, the probability that `(μ - λ) T_N - centring` is at most `w` tends to
`exp (-exp (-w))`, the standard Gumbel distribution function `ProbabilityTheory.gumbelCDF 0 1 w`:
the centred and scaled extinction time converges in distribution to the standard Gumbel law.
(`hQ` records that each `sisRateMatrix` is a rate matrix, which holds since the rates are
nonnegative.)

## Sources

- Brightwell, House and Luczak (2018), Theorem 1.1.
