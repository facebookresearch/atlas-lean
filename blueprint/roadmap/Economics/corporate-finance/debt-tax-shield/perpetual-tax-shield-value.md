# The tax shield on perpetual riskless debt is worth τ·D

For a riskless rate `rD > 0` and any real tax rate `τ` and debt `D`, the present value of the
perpetual tax shield, `∑_{t=1}^{∞} τ * rD * D * (1 + rD)^(-t)` (interest `rD * D` deducted at tax
rate `τ` in every period `t = 1, 2, …`, discounted at the riskless rate `rD`), equals `τ * D`.
Proof sketch: the shield sum is a growing perpetuity with first payment `τ * rD * D`, discount
rate `rD` and growth `0`, so the growing-perpetuity formula `C₁ / (r - g)` gives
`τ * rD * D / rD = τ * D`.
