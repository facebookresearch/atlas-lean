# Numerical example of put–call parity

With one terminal state `ω = 110`, `S0 = 110`, `D = 0`, `K = 100` and `R = 1` (zero interest),
the one-state pricing functional `price(f) = f(110) / 1` gives
`price(call) - price(put) = max(110 - 100, 0) - max(100 - 110, 0) = 10 = (110 - 0) - 100 / 1`,
as put–call parity `C - P = (S0 - D) - K / R` predicts. For another gross return `R > 0`, the
one-state functional `price(f) = f(ω) / R` gives the underlying payoff the price `S0 - D`
exactly when `ω = R * (S0 - D)`.
