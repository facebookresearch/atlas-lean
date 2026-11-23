# Shift of the mean of a trait under selection

For a measure `P` on the sample space, a fitness function `W` of the phenotype vector `Z` and a
trait vector `X` indexed by a finite set `ι`, the selected shift is
`ΔX_i = ∫ W(Z) X_i dP / ∫ W(Z) dP - ∫ X_i dP` for each `i ∈ ι`. When `P` is a probability
measure, `W ≥ 0` and `∫ W(Z) dP > 0`, it is the fitness-weighted mean of `X` minus its mean
before selection. With `X = Z` it is the selection differential `S`; with `X = A` (breeding
values) and faithful additive transmission it is the response `Δz̄`. It is defined for every
measure and fitness function: with the convention `x / 0 = 0` it equals `-∫ X_i dP` when
`∫ W(Z) dP = 0`, and the integral of a non-integrable function counts as `0`.
