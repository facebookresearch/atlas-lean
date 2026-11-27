# For L > 0, differentiating a mode coefficient under the integral sign

Let `L > 0`, let `T` be an open set of times and `V : ℝ → ℝ → ℝ` a function of time and position
such that

- for every `t ∈ T` and `x ∈ [0, L]`, `s ↦ V(s, x)` is differentiable at `t`;
- for every `t ∈ T`, `x ↦ V(t, x)` is continuous on `[0, L]`;
- the time derivative `(t, x) ↦ ∂ₜV(t, x)` is continuous on `T × [0, L]`.

Then for every natural number `n` and every `t ∈ T`, the [cosine coefficient](mode-coeff.md)
`c_n(s) = ∫₀ᴸ V(s, x) cos (n π x / L) dx` is differentiable at `t`, with derivative

`c_n'(t) = ∫₀ᴸ ∂ₜV(t, x) cos (n π x / L) dx`.
