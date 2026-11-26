# Invertible D, continuous forcing: unique solution from consistent data

Let `n` and `m` be finite index sets and `A`, `B`, `C`, `D` real matrices of sizes `n × n`, `n × m`,
`m × n` and `m × m`, with `D` invertible. Let `f : ℝ → ℝⁿ` and `g : ℝ → ℝᵐ` be continuous forcing
paths, let `t₀ ∈ ℝ`, and let `(x₀, y₀) ∈ ℝⁿ × ℝᵐ` be [consistent](consistent-pair.md) at `t₀`:
`C x₀ + D y₀ + g(t₀) = 0`. Write the Schur complement `S = A - B D⁻¹ C` and the
[reduced forcing path](reduced-forcing-path.md) `r(s) = f(s) - B D⁻¹ g(s)`. Then there are
`x : ℝ → ℝⁿ` and `y : ℝ → ℝᵐ` solving the [descriptor system](satisfies-descriptor-system.md) (`x`
differentiable at every time, `x' = A x + B y + f(t)` and `0 = C x + D y + g(t)` for every `t`),
with `x(t₀) = x₀`, `y(t₀) = y₀` and `y` continuous, such that for every real `t`

`x(t) = e^{(t - t₀) S} x₀ + ∫_{t₀}^{t} e^{(t - s) S} r(s) ds` and `y(t) = -D⁻¹ (C x(t) + g(t))`.

Every solution `(x̃, ỹ)` of the descriptor system with `x̃(t₀) = x₀` equals `(x, y)`; no condition
on `ỹ(t₀)` is needed.
