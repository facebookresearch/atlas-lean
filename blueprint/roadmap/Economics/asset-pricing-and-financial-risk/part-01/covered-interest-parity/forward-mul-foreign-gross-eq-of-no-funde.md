# Covered interest parity from no arbitrage

Take a two-currency market with spot rate `S`, forward rate `F`, gross domestic return `R_d`
and gross foreign return `R_f`, finitely many states `ω` (at least one) and any terminal spot
rate `S_T(ω)`. Three assets trade: the domestic deposit (price `1`, payoff `R_d`), one unit of
foreign currency deposited abroad (price `S`, payoff `R_f S_T(ω)`) and a long forward on one
unit of foreign currency (price `0`, payoff `S_T(ω) - F`). If, for some gross funding return
`R > 0`, no portfolio of these assets has a funded gain (payoff minus `R` times cost) that is
nonnegative in every state and strictly positive in some state, then `F R_f = S R_d`. The
covered foreign strategy (one unit of foreign currency, deposited, with `R_f` units sold
forward) pays `F R_f` in every state at cost `S`, and the strictly positive state prices that
exist in the absence of funded arbitrage value it consistently with the domestic deposit.
