# Nonlattice excursion-height tail from the key renewal theorem

Let `P` be a probability measure, `Y` a measurable real random variable, `θ > 0`, and `R`
[nonlattice ladder renewal data](ladder-renewal-data.md) for `Y` and `θ`, with ladder-height
measure `G`. Let `G^θ` be the tilted law with density `e^{θ y}` with respect to `G`, a probability
measure by the ladder Cramér identity. Assume the key renewal theorem for `G^θ`: for every pair of
functions `V, v : ℝ → ℝ` such that `v` is measurable, vanishes on `(-∞, 0)`, is continuous almost
everywhere and is bounded in absolute value on `[0, ∞)` by a nonincreasing integrable function, and
`V` is measurable, vanishes on `(-∞, 0)` and is bounded on every half-line `(-∞, T]`, the renewal
equation `V(t) = v(t) + ∫ V(t - y) dG^θ(y)` for all `t` implies
`V(t) → ∫_0^∞ v(s) ds / ∫ y dG^θ(y)` as `t → ∞`. Then `P(Y > t) e^{θ t} → C` as `t → ∞`, where
`C = C_∞ (1 - E e^{θ D})` is the [excursion-height renewal constant](tail-const.md). This is the
tail condition of a [nonlattice renewal input](nonlattice-renewal-input.md).
