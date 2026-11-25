# Domestic-currency payoff of a covered foreign investment

In a two-currency market with spot rate `S` and forward rate `F` (domestic currency per unit
of foreign currency) and gross foreign return `R_f`, the covered foreign strategy converts
one unit of domestic currency into `1 / S` units of foreign currency, invests them at the
foreign gross return and converts the proceeds back at the locked-in forward rate. Its
terminal domestic payoff is `F R_f / S`, which is `0` when `S = 0` by the convention
`x / 0 = 0`. For `S ≠ 0` and `R_f ≠ 0` it equals the domestic deposit payoff `R_d` (the
gross domestic return) if and only if `F = S R_d / R_f`, that is, when covered interest
parity holds.
