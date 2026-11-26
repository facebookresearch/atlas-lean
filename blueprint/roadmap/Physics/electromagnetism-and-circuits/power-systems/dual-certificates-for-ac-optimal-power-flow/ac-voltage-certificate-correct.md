# Soundness of AC voltage dual certificates

Let `P` be a
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
(a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`) and take an [AC dual witness](acdual-certificate.md) that passes the
[sign check](nonneg.md) (all multipliers nonnegative) and whose [dual slack](dual-slack.md) factors
exactly as `S = F Fᴴ` with its factor `F`. Then, with the
[certified lower bound](certified-lower-bound.md) `L`:

- every relaxation-feasible matrix has
  [relaxation cost](../current-limited-ac-optimal-power-flow-and-its-vo/sdp-cost.md) at least `L`;
- every AC-feasible voltage has
  [AC cost](../current-limited-ac-optimal-power-flow-and-its-vo/ac-cost.md) at least `L`;
- every AC-feasible voltage `V*` whose AC cost equals `L` minimizes the AC cost over all AC-feasible
  voltages, and its lift `V* V*ᴴ` minimizes the relaxation cost over all relaxation-feasible
  matrices.
