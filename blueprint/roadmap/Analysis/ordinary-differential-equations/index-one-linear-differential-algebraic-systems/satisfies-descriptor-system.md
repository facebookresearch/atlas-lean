# Trajectories of a linear descriptor system

Let `n` and `m` be finite index sets and `A`, `B`, `C`, `D` real matrices of sizes `n × n`, `n × m`,
`m × n` and `m × m`, and let `f : ℝ → ℝⁿ` and `g : ℝ → ℝᵐ` be forcing terms and `x : ℝ → ℝⁿ`,
`y : ℝ → ℝᵐ` be a trajectory pair. The pair satisfies the descriptor system when `x` is
differentiable on all of `ℝ` and, at every time `t`,

`x'(t) = A x(t) + B y(t) + f(t)` and `C x(t) + D y(t) + g(t) = 0`.

No regularity is required of `y`.
