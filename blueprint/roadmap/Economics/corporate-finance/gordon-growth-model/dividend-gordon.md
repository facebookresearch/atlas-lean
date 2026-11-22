# Discounted growing payments sum to the first payment over r − g

For real `D₁`, `r`, `g` with `1 + r > 0` and growth ratio `0 ≤ (1 + g) / (1 + r) < 1` (which
imply `-1 ≤ g < r`), the discounted dividends of the stream paying `D₁ * (1 + g)^(t - 1)` at each
date `t ≥ 1` and nothing at date 0 form a summable series with sum
`∑_{t=1}^{∞} D₁ * (1 + g)^(t - 1) / (1 + r)^t = D₁ / (r - g)`.

This is the same result as
[Discounted growing payments sum to the first payment over r − g](../../interest-theory-and-fixed-income/growing-perpetuities/has-sum-growing-perpetuity.md).
Here the terms are indexed by payment date, starting with a zero term at date 0; the linked page
indexes them from the first payment.
