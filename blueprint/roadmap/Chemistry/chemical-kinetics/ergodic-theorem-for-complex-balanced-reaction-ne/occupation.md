# Occupation integral of an observable along a path

For a process `X : ℝ × Ω → σ` with values in a set `σ`, an observable `f : σ → ℝ`, a time `t ∈ ℝ`
and a sample point `ω`, the occupation integral is

`∫_0^t f(X_s(ω)) ds`,

the oriented integral from `0` to `t` with respect to Lebesgue measure: for `t < 0` it is
`-∫_t^0 f(X_s(ω)) ds`. It is `0` when `s ↦ f(X_s(ω))` is not integrable on the interval between `0`
and `t`. For `t > 0`,
divided by `t` it is the time average of `f` along the path up to time `t`. For a jointly measurable
`X`, `t ≥ 0` and `f` the indicator of a measurable set `A`, it is the time the path spends in `A`
before `t`.
