# Index-one reduction of a linear descriptor system

Let `n` and `m` be finite index sets and `A`, `B`, `C`, `D` real matrices of sizes `n × n`, `n × m`,
`m × n` and `m × m`, with `D` invertible, and let `f : ℝ → ℝⁿ` and `g : ℝ → ℝᵐ` be forcing terms and
`x : ℝ → ℝⁿ`, `y : ℝ → ℝᵐ` be a trajectory pair. Then the pair
[satisfies the descriptor system](satisfies-descriptor-system.md)

`x' = A x + B y + f`, `C x + D y + g = 0`

exactly when it [satisfies the reduced system](satisfies-reduced-system.md)

`x' = (A − B D⁻¹ C) x + f − B D⁻¹ g`, `y = −D⁻¹ (C x + g)`,

in both cases with `x` differentiable on `ℝ` and the equations holding at every time. No
regularity is required of `y`.
