# Real and nominal present values agree under the Fisher relation

Let `π` be a constant inflation rate with `1 + π ≠ 0`, `r` a real rate, and `i` the nominal
rate given by the Fisher relation `1 + i = (1 + r)(1 + π)`. For cash flows `c_t` paid at the
dates `t` of a finite set `s ⊆ ℕ`, the nominal flows `(1 + π)ᵗ c_t` discounted at `i` have the
same present value as the real flows `c_t` discounted at `r`:
`∑_{t ∈ s} (1 + i)⁻ᵗ (1 + π)ᵗ c_t = ∑_{t ∈ s} (1 + r)⁻ᵗ c_t`. No condition on `r` is needed:
if `1 + r = 0`, both discount factors are `0` for `t ≥ 1`, by the convention `0⁻¹ = 0`.
