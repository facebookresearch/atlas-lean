# An AC-feasible voltage attaining the certified bound is optimal

Let `P` be a
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`) and take an [AC dual witness](acdual-certificate.md) that passes the
[sign check](nonneg.md) (all multipliers nonnegative) and whose [dual slack](dual-slack.md) factors
exactly as `S = F Fᴴ` with its factor `F`. If a voltage vector `V*` is
[AC feasible](../current-limited-ac-optimal-power-flow-and-its-vo/ac-feasible.md) and its
[AC cost](../current-limited-ac-optimal-power-flow-and-its-vo/ac-cost.md) equals the
[certified lower bound](certified-lower-bound.md) `L`, then `V*` minimizes the AC cost over all
AC-feasible voltages, and its
[lift](../current-limited-ac-optimal-power-flow-and-its-vo/voltage-lift.md) `V Vᴴ` minimizes the
[relaxation cost](../current-limited-ac-optimal-power-flow-and-its-vo/sdp-cost.md) over all
relaxation-feasible matrices. Nothing is assumed about the rank of any other relaxed point.
