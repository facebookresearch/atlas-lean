# Shift of the mean of a trait under selection

For a measure `P` on the sample space, a fitness function `W` of the phenotype vector `Z` and a
trait vector `X` indexed by a finite set `ι`, the selected shift is
`ΔX_i = ∫ W(Z) X_i dP / ∫ W(Z) dP - ∫ X_i dP` for each `i ∈ ι`. When `P` is a probability
measure, `W ≥ 0`, `∫ W(Z) dP > 0`, and `X_i` and `W(Z) X_i` are integrable, it is the
fitness-weighted mean of `X_i` minus its mean before selection. With `X = Z` it is the selection
differential `S`; with `X = A` (breeding values) and faithful additive transmission it is the
response `Δz̄`. It is defined for every measure and fitness function, by two conventions that are
not expectations: `x / 0 = 0`, so it equals `-∫ X_i dP` when `∫ W(Z) dP = 0`, and the integral
of a non-integrable function is set to `0`.
