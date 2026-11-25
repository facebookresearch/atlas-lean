# Layerwise certificate for the Clausius–Clapeyron saturation curve

Let `e_s0 > 0`, `L > 0`, `R_v > 0` and `T₀ > 0`, and let
`p_sat(T) = e_s0 exp((L / R_v)(1 / T₀ - 1 / T))`. Let `n` be a natural number and
`T_face, p_face : ℕ → ℝ` the face temperatures and vapour pressures of `n` layers in series, with
`T_face(i) > 0` for every `i ≤ n` and
`max(p_face(i), p_face(i + 1)) ≤ p_sat(min(T_face(i), T_face(i + 1)))` for every `i < n`. Then for
every layer `i < n` and every `θ ∈ [0, 1]`, the [affine](affine-profile.md) temperature `T` of layer
`i` is positive and its affine vapour pressure is at most `p_sat(T)`. It is the
[layerwise certificate](affine-no-supersaturation-layers.md) for this curve, which is increasing on
positive temperatures; the condition `T₀ > 0` is not used.
