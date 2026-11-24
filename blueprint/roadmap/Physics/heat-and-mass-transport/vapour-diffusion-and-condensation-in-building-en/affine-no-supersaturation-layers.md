# Layerwise certificate against supersaturation in the affine model

Let `p_sat : ℝ → ℝ` be nondecreasing on the positive reals, let `n` be a natural number and let
`T_face, p_face : ℕ → ℝ` be the face temperatures and vapour pressures of `n` layers in series, with
`T_face(i) > 0` for every `i ≤ n` and
`max(p_face(i), p_face(i + 1)) ≤ p_sat(min(T_face(i), T_face(i + 1)))` for every `i < n`. Then for
every layer `i < n` and every `θ ∈ [0, 1]`, the [affine](affine-profile.md) temperature of layer `i`
between `T_face(i)` and `T_face(i + 1)` is positive and the affine vapour pressure of the layer does
not exceed `p_sat` of that temperature.
