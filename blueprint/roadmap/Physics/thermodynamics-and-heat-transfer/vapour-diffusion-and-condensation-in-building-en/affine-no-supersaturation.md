# One-layer certificate against supersaturation in the affine model

Let `p_sat : ℝ → ℝ` be nondecreasing on the positive reals (a saturation-pressure curve of absolute
temperature), let the face temperatures be `T_l > 0`, `T_r > 0` and the face vapour pressures `p_l`,
`p_r`, and suppose `max(p_l, p_r) ≤ p_sat(min(T_l, T_r))`. Then for every `θ ∈ [0, 1]`, the
[affine](affine-profile.md) temperature `T(θ) = (1 - θ) T_l + θ T_r` is positive and the affine
vapour pressure `p(θ) = (1 - θ) p_l + θ p_r` satisfies `p(θ) ≤ p_sat(T(θ))`: the layer is nowhere
supersaturated. This is a sufficient condition for the affine steady model only; it predicts no
condensate and asserts no compliance with a standard.
