# Theta

The theta function `θ(a, b; z) = ∏_γ [z, z₀; γ a, γ b]` attached to `ρ`, as an unconditional
infinite product in `K`. It is normalized at `z₀` only when `z₀` avoids the orbits of `a` and `b`
(`γ a ≠ z₀` and `γ b ≠ z₀` for every `γ`), which the source's theorems assume and this definition
does not: if `z₀ = γ a` or `z₀ = γ b`, the `γ`-th factor is `0`, the product converges to `0`, and
`theta` is this totalized value, not a theta function. It is the limit of the finite products only
when they converge (`ThetaMultipliable`); otherwise `∏'` returns `1`. `K` is a Hausdorff
topological ring, so that this limit is unique (`theta_eq_of_hasProd`). The formula itself does
not use `[IsTopologicalRing K] [T2Space K]`; they only restrict the setting.
