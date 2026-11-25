# Factorial moments of the offspring numbers

For a [Cannings model](../cannings-models/cannings-model.md) `W` of population size `N` and `m ∈ ℕ`,
the `m`-th factorial moment of the offspring numbers is `μ_m = (1/N) ∑_j E[(ν_j)_m]`: the average
over the parents `j` of the expectation, under the law of the parent map `f`, of the falling
factorial `(ν_j)_m = ν_j (ν_j - 1) ⋯ (ν_j - m + 1)` of the
[offspring number](../cannings-models/offspring.md) `ν_j = #{c | f c = j}` (so `(ν)_0 = 1`, and
`(ν)_m = 0` for `m > ν`). By exchangeability in the parents it equals `E[(ν_j)_m]` for every parent
`j` ([every parent has the same offspring factorial moments](factorial-moment-eq.md)). For `N = 0`
there is no parent, the sum is empty and `μ_m = 0`.
