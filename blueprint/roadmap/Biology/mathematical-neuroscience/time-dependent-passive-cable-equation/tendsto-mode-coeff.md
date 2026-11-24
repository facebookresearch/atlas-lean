# For τ > 0, the mode coefficients of a sealed solution tend to 0

Let `τ > 0`, `ℓ` and `L > 0` be real numbers and `V : ℝ → ℝ → ℝ` a function such that

- `V` is a [classical solution](is-cable-solution.md) of `τ ∂ₜV = ℓ² ∂ₓ²V - V` on `[0, L]` at the
  times of `(0, ∞)`, with [sealed ends](sealed-ends.md) at the times of `(0, ∞)`;
- the time derivative `(t, x) ↦ ∂ₜV(t, x)` is continuous on `(0, ∞) × [0, L]`;
- for every `t > 0`, the second spatial derivative `∂ₓ²V(t, ·)` is continuous on `[0, L]`.

Then for every natural number `n` the [cosine coefficient](mode-coeff.md)
`c_n(t) = ∫₀ᴸ V(t, x) cos (n π x / L) dx` tends to `0` as `t → ∞`: by the
[exponential evolution law](mode-coeff-eq-mul-exp.md), `c_n(t) = c_n(1) e^(-k_n (t - 1))` for
`t > 0`, with `k_n > 0` the [rate](decay-rate.md) of the `n`-th mode.
