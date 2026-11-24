# Coefficient matrices of the relaxation constraints

For a
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`), each inequality of the relaxation is written `Re tr(A W) ≤ b`. For bus `k` the
six coefficient matrices are, in order, `A^P_k`, `-A^P_k`, `A^Q_k`, `-A^Q_k`, `E_k` and `-E_k`
(upper and lower active-generation limits, upper and lower reactive-generation limits, upper and
lower squared-voltage limits), where `A^P_k` is the
[active coefficient matrix](../current-limited-ac-optimal-power-flow-and-its-vo/active-coeff.md),
`A^Q_k` the
[reactive coefficient matrix](../current-limited-ac-optimal-power-flow-and-its-vo/reactive-coeff.md)
and `E_k` the
[squared-voltage coefficient matrix](../current-limited-ac-optimal-power-flow-and-its-vo/voltage-coeff.md)
of bus `k`; each branch `e` contributes the
[squared-current coefficient matrix](../current-limited-ac-optimal-power-flow-and-its-vo/branch-current-coeff.md)
of `e`. The right-hand sides are the [constraint bounds](constraint-bound.md).
