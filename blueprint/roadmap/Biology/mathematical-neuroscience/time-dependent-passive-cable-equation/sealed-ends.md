# Sealed-end boundary conditions

For a real number `L`, a set `T` of times and a function `V : ℝ → ℝ → ℝ`, `V` has sealed ends at
`0` and `L` at the times of `T` if for every `t ∈ T`

`∂ₓV(t, 0) = 0` and `∂ₓV(t, L) = 0`:

no axial current flows through either end. The derivative is taken with the convention that it is
`0` where `V(t, ·)` is not differentiable, so the condition is meant together with a
[classical solution](is-cable-solution.md) on `[0, L]`, `L ≥ 0`, which makes `V(t, ·)`
differentiable at both ends.
