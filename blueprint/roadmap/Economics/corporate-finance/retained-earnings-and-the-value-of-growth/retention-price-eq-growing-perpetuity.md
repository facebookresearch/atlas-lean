# Retention price is the value of a growing perpetuity

Let `0 < 1 + r` and `0 ≤ (1 + b * ROE) / (1 + r) < 1` (so the growth `g = b * ROE` satisfies
`-1 ≤ g < r`). Then, for all real `E₁` and `b`, the retention price
`E₁ * (1 - b) / (r - b * ROE)` equals the value of the growing perpetuity that pays the
reinvestment-model dividend `E₁ * (1 - b)` at date 1, growing at rate `b * ROE` per period and
discounted at rate `r`: `∑_{t=1}^{∞} E₁ * (1 - b) * (1 + b * ROE)^(t - 1) / (1 + r)^t`, a
convergent series under these conditions. The condition `0 ≤ (1 + b * ROE) / (1 + r)` matters:
`b = 1 / 2`, `ROE = -8`, `r = 1` gives ratio `-3 / 2` and the discounted flows diverge even though
the rational expression is finite. The value is also an equity price only when the payments
`E₁ * (1 - b)` are nonnegative, e.g. for nonnegative earnings `E₁ ≥ 0` and a retention share
`b ≤ 1`: the identity holds for every `E₁` and `b`, but the payments are negative for positive
earnings and `b > 1`, and for negative earnings and `b < 1` (an algebraic extension, not an
equity value).
