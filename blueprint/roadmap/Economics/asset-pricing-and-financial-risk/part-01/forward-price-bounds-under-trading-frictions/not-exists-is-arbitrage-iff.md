# No arbitrage iff the forward price lies between the carry bounds

In a forward market with spot bid and ask prices `0 < bid ≤ ask`, gross lending and borrowing
rates `0 < R_l ≤ R_b`, income `I` per unit of the underlying paid at maturity and forward
price `F`, there is no arbitrage if and only if `bid · R_l - I ≤ F ≤ ask · R_b - I`. Here an
arbitrage is a static strategy `(x, y, L, B, f)` (`x` units bought at the ask, `y` sold short
at the bid, cash `L` lent, cash `B` borrowed, `f` units of a long forward) with
`x, y, L, B ≥ 0` and `x - y + f = 0` whose cash flows `bid · y + B - ask · x - L` at time `0`
and `(x - y) I + R_l L - R_b B - f F` at maturity are both nonnegative, at least one of them
strictly positive.
