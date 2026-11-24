# Derivative of present value in the yield

For cash flows `c_t` (any real numbers) paid at the dates `t` of a finite set `s ⊆ ℕ`, the
present value `P(r) = ∑_{t ∈ s} c_t (1 + r)⁻ᵗ` at a constant yield `r` is differentiable at
every `r₀ > -1`, with derivative `P′(r₀) = -(∑_{t ∈ s} t c_t (1 + r₀)⁻ᵗ) / (1 + r₀)`.
