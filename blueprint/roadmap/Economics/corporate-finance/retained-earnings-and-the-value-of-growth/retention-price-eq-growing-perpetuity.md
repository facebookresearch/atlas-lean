# Retention price is the value of a growing perpetuity

`retentionPrice` is the value of the growing perpetuity that pays the
reinvestment-model dividend `E₁ * (1 - b)` growing at `retentionGrowth b ROE`, under the
convergence hypotheses of `growingPerpetuity_eq`. In particular, the rational
expression is an equity price only when `0 ≤ (1 + b * ROE) / (1 + r)`; without this,
e.g. `b = 1 / 2`, `ROE = -8`, `r = 1` gives ratio `-3 / 2` and the discounted flows
diverge even though the rational expression is finite. It is also an equity price only
when the payments `E₁ * (1 - b)` are nonnegative, e.g. for nonnegative earnings `E₁ ≥ 0`
and a retention share `b ≤ 1`: the identity holds for every `E₁` and `b`, but the
payments are negative for positive earnings and `b > 1`, and for negative earnings and
`b < 1` (an algebraic extension, not an equity value).
