# The retention price exceeds the no-growth price iff `ROE > r`

**The retention price exceeds the no-growth price iff `ROE > r`** (an algebraic
extension of value creation by retained earnings). With positive earnings, a positive
retention parameter `b`, a positive required return, growth below the required return
(`b * ROE < r`, so the Gordon denominator is positive), and the convergence
hypothesis `0 ≤ (1 + b * ROE) / (1 + r)` (so the retention price is the value of a
convergent growing perpetuity, via `retentionPrice_eq_growingPerpetuity`), the
retention price exceeds the no-growth price exactly when the reinvestment return
exceeds the required return. The statement does not assume `b ≤ 1`, so it extends
past the retention-share domain: for `b > 1` the "dividend" `E₁ * (1 - b)` is negative
and the comparison is between formulas, not equity values. On the retention-share
domain `0 < b ≤ 1` it says that retained earnings create value iff `ROE > r`.
