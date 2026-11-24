# Objective matrix of the AC power flow relaxation

For a
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`), the objective matrix is `C = Σ_k c_k A^P_k`, where `A^P_k` is the
[active coefficient matrix](../current-limited-ac-optimal-power-flow-and-its-vo/active-coeff.md) of
bus `k`. The relaxation cost of a matrix `W` is `Re tr(C W) + c₀`
([cost identity](sdp-cost-eq-objective.md)), with the [constant term](objective-offset.md) `c₀`.
