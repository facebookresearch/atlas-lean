# Classical solution of the passive cable equation on a finite cable

Let `τ`, `ℓ` and `L` be real numbers, `T` a set of times and `V : ℝ → ℝ → ℝ` a function of time
and position. Then `V` is a classical solution of the passive cable equation

`τ ∂ₜV = ℓ² ∂ₓ²V - V`

on the cable `[0, L]` at the times of `T` if, for every `t ∈ T` and every `x ∈ [0, L]`:

- `s ↦ V(s, x)` is differentiable at `t`;
- `y ↦ V(t, y)` is differentiable at `x`, and so is its derivative `∂ₓV(t, ·)`;
- `τ ∂ₜV(t, x) = ℓ² ∂ₓ²V(t, x) - V(t, x)`, where `∂ₓ²V(t, ·)` is the derivative of `∂ₓV(t, ·)`.

All derivatives are two-sided, also at the ends `x = 0` and `x = L` and at the ends of `T`: `V` is
a function on all of `ℝ²`. No initial or boundary condition is part of the definition. When
`L < 0` the interval `[0, L]` is empty and every `V` qualifies. In the model `τ`, `ℓ` and `L` are
positive, `τ` being the membrane time constant and `ℓ` the length constant.
