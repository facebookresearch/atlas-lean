# For nonzero total resistance, the last interface pressure is p_out

Let `n` be a natural number and `R : ℕ → ℝ` layer resistances with `∑_{i < n} R_i ≠ 0`, and let
`p_in`, `p_out` be real numbers. Then the [interface pressure](vapor-interface-pressure.md) after
all `n` layers is `p_n = p_out`. Equivalently, since `p_n = p_in - g ∑_{i < n} R_i` with the
[steady series flux](vapor-series-flux.md) `g`, the flux times the total resistance is the drop:
`g ∑_{i < n} R_i = p_in - p_out`. With zero total resistance the flux is `0` by the convention
`u / 0 = 0` and `p_n = p_in` instead.
