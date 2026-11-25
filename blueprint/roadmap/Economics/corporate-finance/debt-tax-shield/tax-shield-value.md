# Present value of interest tax shields on perpetual debt

For a real tax rate `τ`, riskless rate `rD` and debt `D`, the present value of the perpetual tax
shield on riskless debt is `∑_{t=1}^{∞} τ * rD * D * (1 + rD)^(-t)`: in each period
`t = 1, 2, …` the firm deducts interest `rD * D` at tax rate `τ`, saving `τ * rD * D`, discounted
at the riskless rate `rD`. The series converges for `rD > 0`; the infinite sum is taken to be `0`
when the series does not converge, and `(1 + rD)^(-t)` is read as `0` when `rD = -1`
(convention `0⁻¹ = 0`).
