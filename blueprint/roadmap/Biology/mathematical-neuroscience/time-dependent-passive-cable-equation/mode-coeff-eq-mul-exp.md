# For L > 0, mode coefficients of sealed solutions evolve exponentially

Let `τ ≠ 0`, `ℓ` and `L > 0` be real numbers, `T` an open preconnected set of times (an open
interval, possibly unbounded) and `V : ℝ → ℝ → ℝ` a function such that

- `V` is a [classical solution](is-cable-solution.md) of `τ ∂ₜV = ℓ² ∂ₓ²V - V` on `[0, L]` at the
  times of `T`, with [sealed ends](sealed-ends.md) at the times of `T`;
- the time derivative `(t, x) ↦ ∂ₜV(t, x)` is continuous on `T × [0, L]`;
- for every `t ∈ T`, the second spatial derivative `∂ₓ²V(t, ·)` is continuous on `[0, L]`.

Then for every natural number `n` and all times `t, t₀ ∈ T`, the
[cosine coefficient](mode-coeff.md) `c_n(t) = ∫₀ᴸ V(t, x) cos (n π x / L) dx` evolves as

`c_n(t) = c_n(t₀) e^(-k_n (t - t₀))`,

where `k_n` is the [rate](decay-rate.md) of the `n`-th mode. Both times must lie in `T`. For
`τ > 0` this is decay at rate `k_n > 0` ([limit](tendsto-mode-coeff.md)); for `τ < 0`,
`k_0 = 1 / τ < 0` and a nonzero uniform coefficient grows.
