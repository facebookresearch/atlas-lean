# For each start in an inward box, a trapped radiator solution exists

Let `C > 0`, `K_rad > 0`, `0 ≤ T_min ≤ T_max` and `Q` satisfy the inward end conditions
`Q - K_rad T_min⁴ ≥ 0` and `Q - K_rad T_max⁴ ≤ 0`, and let `T₀ ∈ [T_min, T_max]`. Then there is
`T : ℝ → ℝ` with `T(0) = T₀` such that:

- at every real `t`, `T` has derivative equal to the [clipped radiator rate](clipped-radiator-rate.md)
  at `T(t)`;
- at every `t ≥ 0`, `T(t) ∈ [T_min, T_max]` and `T` has derivative `(Q - K_rad T(t)⁴) / C`, the
  [radiator rate](radiator-rate.md).
