# Zero probability flux (Wright 1931)

On `(0, 1)` the Beta`(θ₁, θ₂)` density `π`
satisfies `½ (x (1 - x) π)' - (θ₁ (1 - x) - θ₂ x) / 2 · π = 0`. The identity holds for all real
`θ₁, θ₂` (it is linear in `π`; Mathlib's density is identically `0` when `B(θ₁, θ₂) = 0`);
`π` is a probability density when `θ₁, θ₂ > 0` (`isProbabilityMeasureBeta`).
