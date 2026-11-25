# Every constraint coefficient matrix is Hermitian

For every
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`) and every index `i` in the order of the [enumeration](constraint-index.md) of
the `6 n_N + n_E` constraints, the [coefficient matrix](lifted-coeff.md) `A_i` is Hermitian.
