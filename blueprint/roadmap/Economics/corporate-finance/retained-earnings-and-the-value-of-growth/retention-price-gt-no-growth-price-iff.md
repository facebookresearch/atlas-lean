# The retention price exceeds the no-growth price iff ROE > r

Let `E₁ > 0` (earnings), `b > 0` (retention parameter), `r > 0` (required return),
`b * ROE < r` (growth below the required return, so the Gordon denominator is positive) and
`0 ≤ (1 + b * ROE) / (1 + r)` (so the retention price is the value of a convergent growing
perpetuity). Then the retention price exceeds the no-growth price,
`E₁ * (1 - b) / (r - b * ROE) > E₁ / r`, exactly when the reinvestment return exceeds the
required return, `ROE > r`. The statement does not assume `b ≤ 1`, so it extends past the
retention-share domain: for `b > 1` the "dividend" `E₁ * (1 - b)` is negative and the comparison
is between formulas, not equity values. On the retention-share domain `0 < b ≤ 1` it says that
retained earnings create value iff `ROE > r`.
