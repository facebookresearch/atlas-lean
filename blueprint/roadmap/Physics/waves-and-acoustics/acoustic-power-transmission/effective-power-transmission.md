# Effective power transmission coefficient of a set of patches

For a finite set `s` of patches, with incident intensity `I i`, area `A i` and transmission
coefficient `τ i` on patch `i` (any real values), the effective power transmission coefficient
is the centre of mass of the coefficients with weights `I i * A i`:
`τ_eff = (∑_{i ∈ s} I i * A i)⁻¹ * ∑_{i ∈ s} I i * A i * τ i`, the total transmitted power over
the total incident power ([quotient form](effective-power-transmission-eq.md)). With the
convention `0⁻¹ = 0` it is `0` when the total incident power `∑_{i ∈ s} I i * A i` is `0`, for
example when `s` is empty. In the physical reading the intensities and areas are positive and
`0 < τ i ≤ 1`, so on a nonempty set the weights are positive and `τ_eff` is a weighted average of
the coefficients; the definition takes any real values.
