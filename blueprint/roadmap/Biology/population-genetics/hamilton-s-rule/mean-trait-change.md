# Change in mean trait

For a finite set of individuals with fitnesses `w i`, parental traits `z i` and mean offspring
traits `z' i` (all real), the change in mean trait from parents to offspring is
`Δz̄ = (∑ i, w i * z' i) / (∑ i, w i) - 𝔼 i, z i`: the fitness-weighted mean of the offspring
traits minus the average parental trait, where `𝔼 i` is the average over the individuals. It is
defined for all real `w`, `z` and `z'`: when `∑ i, w i = 0` the convention `x / 0 = 0` makes the
first term `0`, so that `Δz̄ = -𝔼 i, z i`; for an empty set of individuals that average is `0`
too, so that `Δz̄ = 0`. The intended domain is `∑ i, w i ≠ 0`, for example
nonnegative offspring numbers with a positive total, where the first term is the mean trait of the
offspring generation.
