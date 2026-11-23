# Value of a growing perpetuity

The value of a growing perpetuity with first payment `C₁` at date 1, growth rate `g` and constant
discount rate `r` is the sum of all its discounted cash flows,
`∑_{t=0}^{∞} C₁ (1 + g)ᵗ (1 + r)^{-(t+1)}`, for all real `C₁`, `r` and `g`. When this series does
not converge absolutely, the value is `0` by convention. For `r = -1` the convention `0⁻¹ = 0` makes
every discount factor, hence the value, `0`; the intended domain is `1 + r > 0` with
`0 ≤ (1 + g) / (1 + r) < 1`, on which the series converges to `C₁ / (r - g)`.
