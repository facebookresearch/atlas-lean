# Admissible strategy with no net exposure at maturity

A static strategy `(x, y, L, B, f)` (units bought at the ask, units sold short at the bid,
cash lent, cash borrowed, long forward units) is admissible when its trade sizes are
nonnegative, `x ≥ 0`, `y ≥ 0`, `L ≥ 0` and `B ≥ 0`, and it is hedged: its net exposure to the
underlying at maturity, `x - y + f`, is zero, so its payoff does not depend on the terminal
spot price.
