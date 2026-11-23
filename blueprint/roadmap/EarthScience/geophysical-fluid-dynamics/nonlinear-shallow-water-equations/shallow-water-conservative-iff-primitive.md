# Shallow water conservative iff primitive

Conservative and primitive forms of 1D flat-bed frictionless
shallow water agree at a wet point. Let `h` be the depth and `u` the
velocity, with time and space slices differentiable at `(t, x)` with
partials `hₜ`, `hₓ`, `uₜ`, `uₓ`, and let the depth be positive there.
Then mass and momentum conservation, `∂ₜh + ∂ₓ(h u) = 0` and
`∂ₜ(h u) + ∂ₓ(h u² + g h² / 2) = 0`, hold at `(t, x)` if and only if
`hₜ + u hₓ + h uₓ = 0` and `uₜ + u uₓ + g hₓ = 0` hold there. Classical
pointwise statement; no weak solutions.
