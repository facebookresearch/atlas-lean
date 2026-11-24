# Continuous forcing: unique global reduced-state solution through x₀

Let `n` and `m` be finite index sets and `A`, `B`, `C`, `D` real matrices of sizes `n × n`, `n × m`,
`m × n` and `m × m`, with `D` invertible. Let `f : ℝ → ℝⁿ` and `g : ℝ → ℝᵐ` be continuous forcing
paths, let `t₀ ∈ ℝ` and `x₀ ∈ ℝⁿ`, and write the Schur complement `S = A - B D⁻¹ C` and the
[reduced forcing path](reduced-forcing-path.md) `r(s) = f(s) - B D⁻¹ g(s)`. Then there is
`x : ℝ → ℝⁿ` with `x(t₀) = x₀`, given for every real `t` by the variation-of-constants formula

`x(t) = e^{(t - t₀) S} x₀ + ∫_{t₀}^{t} e^{(t - s) S} r(s) ds`

(an oriented integral, so `∫_{t₀}^{t} = -∫_{t}^{t₀}` for `t < t₀`), with derivative
`x'(t) = S x(t) + r(t)` at every `t`. Every `x̃ : ℝ → ℝⁿ` with `x̃(t₀) = x₀` and derivative
`x̃'(t) = S x̃(t) + r(t)` at every `t` equals `x`.
