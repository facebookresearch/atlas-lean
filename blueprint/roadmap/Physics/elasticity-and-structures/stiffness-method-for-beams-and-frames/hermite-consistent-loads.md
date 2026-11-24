# Hermite consistent loads

Consistent load vector for a uniform span load. For span
`L ≠ 0` and constant load `w`, integrating the four Hermite shape
functions (in `ξ = x / L`, in the interleaved nodal order
`[v₁, θ₁, v₂, θ₂]`: end-1 deflection, end-1 rotation, end-2
deflection, end-2 rotation) against `w` over `[0, L]` gives the
consistent nodal load vector
`(w * L / 2, w * L ^ 2 / 12, w * L / 2, -w * L ^ 2 / 12)`: the two
vertical entries sum to the total load `w * L`, and the moment
entries are equal in magnitude and opposite in sign.
