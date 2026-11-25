# The relaxation cost in terms of the objective matrix

For every
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`) and every complex `n_N × n_N` matrix `W`, the
[relaxation cost](../current-limited-ac-optimal-power-flow-and-its-vo/sdp-cost.md) of `W` is
`Re tr(C W) + c₀`, with the [objective matrix](objective-matrix.md) `C` and the
[constant term](objective-offset.md) `c₀`.
