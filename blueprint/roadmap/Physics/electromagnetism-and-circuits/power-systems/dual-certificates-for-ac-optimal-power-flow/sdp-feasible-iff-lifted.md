# Relaxation feasibility in enumerated constraint form

For every
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`) and every complex `n_N × n_N` matrix `W`, `W` is
[relaxation feasible](../current-limited-ac-optimal-power-flow-and-its-vo/sdp-feasible.md) if and
only if `W` is positive semidefinite and `Re tr(A_i W) ≤ b_i` for every index `i` in the order of
the [enumeration](constraint-index.md) of the `6 n_N + n_E` constraints, with the
[coefficient matrices](lifted-coeff.md) `A_i` and [right-hand sides](lifted-bound.md) `b_i`.
