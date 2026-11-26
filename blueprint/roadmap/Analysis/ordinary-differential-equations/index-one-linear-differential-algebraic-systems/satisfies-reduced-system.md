# Trajectories of the reduced system with reconstruction

Let `n` and `m` be finite index sets and `A`, `B`, `C`, `D` real matrices of sizes `n × n`, `n × m`,
`m × n` and `m × m`, with `D` invertible, and let `f : ℝ → ℝⁿ` and `g : ℝ → ℝᵐ` be forcing terms and
`x : ℝ → ℝⁿ`, `y : ℝ → ℝᵐ` be a trajectory pair. The pair satisfies the reduced system when `x` is
differentiable on all of `ℝ` and, at every time `t`,

`x'(t) = (A − B D⁻¹ C) x(t) + f(t) − B D⁻¹ g(t)` and `y(t) = −D⁻¹ (C x(t) + g(t))`:

the Schur-complement differential equation with the
[reduced forcing](reduced-forcing.md), and the
[reconstruction](algebraic-reconstruction.md) of the algebraic variable.
