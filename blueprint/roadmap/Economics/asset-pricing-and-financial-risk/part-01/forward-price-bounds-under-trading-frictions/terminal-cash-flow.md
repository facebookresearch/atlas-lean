# Terminal cash flow of a hedged strategy

In a forward market with gross lending rate `R_l`, gross borrowing rate `R_b`, income `I` per
unit of the underlying paid at maturity and forward price `F`, the cash received at maturity
by a static strategy `(x, y, L, B, f)` (units bought at the ask, units sold short at the bid,
cash lent, cash borrowed, long forward units) is `(x - y) I + R_l L - R_b B - f F`: net income
on the underlying position, loan repayments received and paid, and the forward's delivery
payment `-f F`. The terminal spot value `(x - y + f) S_T` of the position, where `S_T` is the
spot price at maturity, is not included; it vanishes for a hedged strategy, one with
`x - y + f = 0`.
