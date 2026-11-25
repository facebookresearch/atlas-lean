# Descriptor trajectories satisfy the reduced differential equation

Let `n` and `m` be finite index sets and `A`, `B`, `C`, `D` real matrices of sizes `n × n`, `n × m`,
`m × n` and `m × m`, with `D` invertible, and let `f : ℝ → ℝⁿ` and `g : ℝ → ℝᵐ` be forcing terms and
`x : ℝ → ℝⁿ`, `y : ℝ → ℝᵐ` be a trajectory pair that
[satisfies the descriptor system](satisfies-descriptor-system.md). Then at every time `t`

`x'(t) = (A − B D⁻¹ C) x(t) + f(t) − B D⁻¹ g(t)`.
