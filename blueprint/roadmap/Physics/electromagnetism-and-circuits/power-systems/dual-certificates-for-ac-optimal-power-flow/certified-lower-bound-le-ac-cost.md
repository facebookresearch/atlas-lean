# A checked AC dual witness bounds the AC cost

Let `P` be a
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`) and take an [AC dual witness](acdual-certificate.md) that passes the
[sign check](nonneg.md) (all multipliers nonnegative) and whose [dual slack](dual-slack.md) factors
exactly as `S = F Fᴴ` with its factor `F`. Then every voltage vector `V` that is
[AC feasible](../current-limited-ac-optimal-power-flow-and-its-vo/ac-feasible.md) has
[AC cost](../current-limited-ac-optimal-power-flow-and-its-vo/ac-cost.md) at least the
[certified lower bound](certified-lower-bound.md) `L`: its
[lift](../current-limited-ac-optimal-power-flow-and-its-vo/voltage-lift.md) `V Vᴴ` is relaxation
feasible with the same cost.
