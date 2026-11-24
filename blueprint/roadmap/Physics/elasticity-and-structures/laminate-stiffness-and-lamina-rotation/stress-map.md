# Stress transformation to material axes

For a real angle `θ`, with `c = cos θ` and `s = sin θ`, the matrix

`T_s(θ) = [[c², s², 2 c s], [s², c², −2 c s], [−c s, c s, c² − s²]]`.

It maps the global stress components `(σ_xx, σ_yy, τ_xy)` to the components `(σ₁₁, σ₂₂, τ₁₂)` in
material axes at the angle `θ` ([rotation of the stress](stress-map-mul-vec-stress-voigt.md)). It
differs from the [strain map](strain-map.md) in the placement of the factors `2`.
