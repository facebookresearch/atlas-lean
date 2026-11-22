# Derivative of present value in the yield (restated)

For cash flows `c_t` (any real numbers) paid at the dates `t` of a finite set `s ⊆ ℕ`, the
price `P(r) = ∑_{t ∈ s} c_t (1 + r)⁻ᵗ` is differentiable at every yield `r > -1`, with the
derivative obtained term by term: `P′(r) = -∑_{t ∈ s} t c_t (1 + r)^{-t-1}`.

This is the same result as
[Derivative of present value in the yield](has-deriv-at-present-value-discount-fact.md). Here the
derivative is written term by term as `-∑_{t ∈ s} t c_t (1 + r)^{-t-1}`; the linked page writes it
as `-(∑_{t ∈ s} t c_t (1 + r₀)⁻ᵗ) / (1 + r₀)`.
