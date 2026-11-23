# Persistence Eq

The **persistence equilibrium** `p* = 1 - e / c`: for `c ≠ 0`, the equilibrium besides
`p = 0` (`balance_eq_zero_iff`). At `c = 0` it is not an equilibrium unless `e = 0`: Lean's
division gives `persistenceEq 0 e = 1`, while `balance 0 e 1 = -e`.
