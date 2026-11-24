# Dual slack matrix of an AC dual witness

For a
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`) and an [AC dual witness](acdual-certificate.md), the dual slack matrix is

`S = C + Σ_b (μ^P_max,b - μ^P_min,b) A^P_b + Σ_b (μ^Q_max,b - μ^Q_min,b) A^Q_b`
`+ Σ_b (μ^V_max,b - μ^V_min,b) E_b + Σ_e μ^I_e A^I_e`,

where `C` is the [objective matrix](objective-matrix.md), `μ` the multipliers of the witness, and
`A^P_b`, `A^Q_b`, `E_b`, `A^I_e` the
[active coefficient matrix](../current-limited-ac-optimal-power-flow-and-its-vo/active-coeff.md),
[reactive coefficient matrix](../current-limited-ac-optimal-power-flow-and-its-vo/reactive-coeff.md),
[squared-voltage coefficient matrix](../current-limited-ac-optimal-power-flow-and-its-vo/voltage-coeff.md)
and
[squared-current coefficient matrix](../current-limited-ac-optimal-power-flow-and-its-vo/branch-current-coeff.md).
It is `C + Σ_i λ_i A_i` over the enumerated constraints
([enumerated form](dual-slack-eq-lifted.md)).
