# Möhle–Sagitov conditions for a Kingman genealogy limit

A sequence of [Cannings models](../cannings-models/cannings-model.md) `W_N`, one of population size
`N` for every `N ∈ ℕ`, satisfies the Möhle–Sagitov conditions for a Kingman genealogy limit (Möhle
2000; Möhle–Sagitov 2001) when its [pair-coalescence probabilities](pair-coalescence.md)
`c_N = μ_2 / (N - 1)` are positive for all sufficiently large `N` and tend to `0` (so that
`⌊t / c_N⌋` generations is a nondegenerate time scale), and triple mergers are negligible on that
time scale: `μ_3 / (N² c_N) → 0` as `N → ∞`. Here `μ_m = (1/N) ∑_j E[(ν_j)_m]` is the `m`-th
[factorial moment](factorial-moment.md) of the offspring numbers `ν_j` of `W_N`, so that
`μ_2 = E[ν_j (ν_j - 1)]` and `μ_3 = E[ν_j (ν_j - 1) (ν_j - 2)]` for every parent `j`.

The conditions concern large `N` only, and `c_N` is `0` for `N ≤ 1`: at `N = 0` there is no parent
and `μ_m = 0`, and at `N = 1`, `N - 1 = 0` and `x / 0 = 0`. Wherever `c_N = 0`, the quotient
`μ_3 / (N² c_N)` is `0` by the same convention.
