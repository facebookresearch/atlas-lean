# Node current balance of the buck network

For real numbers `R` and `C`, functions `i, v : ℝ → ℝ` and a time `t` with
`C v'(t) = i(t) - v(t) / R`, the [branch currents](buck-branch-current.md) `(I₀, I₁, I₂, I₃)` at
`(i(t), v'(t), v(t))` satisfy `I₂ + I₃ = I₁` (output node) and `I₀ + I₁ = 0` (input node). Here
`v'(t)` is the derivative of `v` at `t`, taken to be `0` where `v` is not differentiable.
