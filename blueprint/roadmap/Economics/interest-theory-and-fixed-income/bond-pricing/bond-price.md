# Price of a coupon bond at a constant yield

The price at per-period rate `r` of a bond with coupon `c`, face value `F` and maturity `n` is
the present value of its cash flows over the payment dates `1, …, n`:
`∑_{t=1}^{n} (1 + r)⁻ᵗ (c + [t = n] F)`, where `[t = n] F` is `F` at maturity and `0` before.
The sum is empty, so the price is `0`, when `n = 0`; the discount factor uses the convention
`0⁻¹ = 0` when `r = -1`.
