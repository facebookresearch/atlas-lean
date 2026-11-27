# Arbitrage opportunity in a forward market with frictions

In a forward market with spot bid and ask prices `bid` and `ask`, gross lending and borrowing
rates `R_l` and `R_b`, income `I` per unit of the underlying paid at maturity and forward
price `F`, an arbitrage is a static strategy `(x, y, L, B, f)` (units bought at the ask, units
sold short at the bid, cash lent, cash borrowed, long forward units) that is admissible
(`x, y, L, B ≥ 0` and `x - y + f = 0`) and whose cash flows at both dates, the initial
`bid · y + B - ask · x - L` and the terminal `(x - y) I + R_l L - R_b B - f F`, are
nonnegative, at least one of them strictly positive.
