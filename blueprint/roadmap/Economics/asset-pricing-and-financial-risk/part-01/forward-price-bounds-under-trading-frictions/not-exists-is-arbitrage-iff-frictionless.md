# Without frictions, no arbitrage iff F is the cost-of-carry price

In a forward market without a bid-ask spread or a borrowing-lending wedge, with spot bid and
ask prices `bid = ask = S > 0`, gross lending and borrowing rates `R_l = R_b = R > 0`, income
`I` per unit of the underlying paid at maturity and forward price `F`, there is no arbitrage
if and only if `F = S R - I`, the cost-of-carry price. Here an arbitrage is a static strategy
`(x, y, L, B, f)` (`x` units bought, `y` sold short, cash `L` lent, cash `B` borrowed, `f`
units of a long forward) with `x, y, L, B ≥ 0` and `x - y + f = 0` whose cash flows
`S y + B - S x - L` at time `0` and `(x - y) I + R L - R B - f F` at maturity are both
nonnegative, at least one of them strictly positive.
