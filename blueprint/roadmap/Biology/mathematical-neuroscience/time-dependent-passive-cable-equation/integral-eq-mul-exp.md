# Total potential of a sealed solution evolves at the membrane rate

Let `τ ≠ 0`, `ℓ` and `L > 0` be real numbers, `T` an open preconnected set of times (an open
interval, possibly unbounded) and `V : ℝ → ℝ → ℝ` a function such that

- `V` is a [classical solution](is-cable-solution.md) of `τ ∂ₜV = ℓ² ∂ₓ²V - V` on `[0, L]` at the
  times of `T`, with [sealed ends](sealed-ends.md) at the times of `T`;
- the time derivative `(t, x) ↦ ∂ₜV(t, x)` is continuous on `T × [0, L]`;
- for every `t ∈ T`, the second spatial derivative `∂ₓ²V(t, ·)` is continuous on `[0, L]`.

Then for all times `t, t₀ ∈ T` the total potential evolves as

`∫₀ᴸ V(t, x) dx = (∫₀ᴸ V(t₀, x) dx) e^(-(t - t₀)/τ)`.

This is the [exponential evolution law](mode-coeff-eq-mul-exp.md) of the uniform mode, whose rate
is `1 / τ`. For `τ > 0` the total potential decays at exactly the membrane rate `1 / τ`; for
`τ < 0` a nonzero total potential grows.
