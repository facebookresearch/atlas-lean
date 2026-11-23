# PRDS fails for the coupled two-gene family

With `m = 2` genes and the mean estimate
`λ̂`, the `χ²₁` p-values `pⱼ = P(χ²₁ > Sⱼ / λ̂)` are not PRDS on any set of true nulls
containing gene `0`, as soon as both `{T₀ ≥ 1}` and `{T₀ < 1}` have positive probability and
the scores do not vanish simultaneously (almost surely). No independence, Gaussianity or other
assumption on the scores is involved: `T₁ = 2 - T₀` makes `p₁` a decreasing function of `p₀`.
