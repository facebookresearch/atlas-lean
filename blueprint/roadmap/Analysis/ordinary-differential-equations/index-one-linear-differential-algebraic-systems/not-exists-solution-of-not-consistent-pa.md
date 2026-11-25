# An inconsistent initial pair is reached by no descriptor solution

Let `n` and `m` be finite index sets, `A`, `B`, `C`, `D` real matrices of sizes `n × n`, `n × m`,
`m × n` and `m × m`, `f : ℝ → ℝⁿ` and `g : ℝ → ℝᵐ`, with no invertibility or continuity assumed. If
`(x₀, y₀)` is not [consistent](consistent-pair.md) at `t₀`, that is `C x₀ + D y₀ + g(t₀) ≠ 0`, then
no solution `(x, y)` of the [descriptor system](satisfies-descriptor-system.md) (`x` differentiable
at every time, `x' = A x + B y + f(t)` and `0 = C x + D y + g(t)` for every `t`) has `x(t₀) = x₀`
and `y(t₀) = y₀`.
