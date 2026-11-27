# Replicator trajectory of a Lotka–Volterra solution

For a finite set `ι`, a curve `y : ℝ → (ι → ℝ)` and a real `s`, the replicator trajectory at time
`s` is the [replicator coordinate vector](of-lv.md) `(1, y) / (1 + ∑_j y_j)` of `y(t⁻¹(s))`, where
`t(·)` is the [replicator time](rep-time-change.md) and `t⁻¹` a chosen inverse of it: the true
inverse on its range when it is injective, and an unspecified value off the range. With the
convention `a / 0 = 0`, every coordinate is `0` when `1 + ∑_j y_j(t⁻¹(s)) = 0`.
