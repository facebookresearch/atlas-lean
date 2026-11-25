# Gumbel limit from ladder renewal data, nonlattice scores

Let `P` be a probability measure and `X 0, X 1, …` real scores satisfying the
[Cramér conditions](cramer-scores.md) with root `θ` and the nonlattice condition (for no `h > 0`
does `X 0` lie almost surely on `hℤ`). Let `L` be a [ladder input](ladder-input.md) for their
[maximal segment scores](max-segment-score-rv.md) `Mₙ`, with mean excursion length `A > 0`, and `R`
[nonlattice ladder renewal data](ladder-renewal-data.md) for its first excursion height, with
ladder-height measure `G`, and let `G^θ` be the tilted law with density `e^{θ y}` with respect to
`G`. Assume the key renewal theorem for `G^θ`: for every pair of functions `V, v : ℝ → ℝ` such that
`v` is measurable, vanishes on `(-∞, 0)`, is continuous almost everywhere and is bounded in
absolute value on `[0, ∞)` by a nonincreasing integrable function, and `V` is measurable, vanishes
on `(-∞, 0)` and is bounded on every half-line `(-∞, T]`, the renewal equation
`V(t) = v(t) + ∫ V(t - y) dG^θ(y)` for all `t` implies `V(t) → ∫_0^∞ v(s) ds / ∫ y dG^θ(y)` as
`t → ∞`. Then for every real `x`, `P(Mₙ ≤ log n / θ + x) → exp(-K e^{-θ x})` with `K = C / A` and
`C = C_∞ (1 - E e^{θ D})` the [excursion-height renewal constant](tail-const.md).
