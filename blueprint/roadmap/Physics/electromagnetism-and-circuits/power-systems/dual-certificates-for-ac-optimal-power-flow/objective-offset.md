# Constant term of the relaxation objective

For a
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`), the constant term of the objective is `c₀ = Σ_k c_k P_d,k`, where `P_d,k` is
the active demand at bus `k`.
