# Retention price as a Gordon formula

For all real `E₁`, `b`, `ROE`, `r`, the retention price `E₁ * (1 - b) / (r - b * ROE)` is exactly
the Gordon formula `D₁ / (r - g)` with the reinvestment-model dividend `D₁ = E₁ * (1 - b)` and
growth `g = b * ROE` substituted in (both sides with the convention x / 0 = 0). This is an
algebraic identity; on its own it does not say the discounted cash flows converge. The price
interpretation needs the growing-perpetuity conditions `0 < 1 + r` and
`0 ≤ (1 + b * ROE) / (1 + r) < 1`, under which the retention price is the value of the
corresponding growing perpetuity.
