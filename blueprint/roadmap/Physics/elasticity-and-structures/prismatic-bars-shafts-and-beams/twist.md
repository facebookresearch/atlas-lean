# Twist

Torsional port: a circular shaft fixed at `x = 0`, with distributed torque `t` and end torque
`T` at `x = L`, is the same problem with `k = GJ`. Its twist equals
`fixedTractionDisplacement GJ L T t` on `[0, L]` and its internal torque is
`GJ * φ' x = T + ∫ y in x..L, t y`, by the bar lemmas; no second solver is used.
