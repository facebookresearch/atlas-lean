# Certified lower bound of an AC dual witness

For a
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`) and an [AC dual witness](acdual-certificate.md), the certified lower bound is
`L = c₀ - Σ_i λ_i b_i`, where `c₀` is the [constant term](objective-offset.md), `λ_i` the
multipliers and `b_i` the [right-hand sides](constraint-bound.md) of the constraints
([enumerated form](certified-lower-bound-eq-lifted.md)). For a witness that passes the sign check
and factors its dual slack, it bounds the relaxation and AC costs from below
([soundness](ac-voltage-certificate-correct.md)).
