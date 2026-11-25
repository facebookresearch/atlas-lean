# The dual slack in enumerated constraint form

For every
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`) and [AC dual witness](acdual-certificate.md), the [dual slack](dual-slack.md)
equals `C + Σ_i λ_i A_i`, with the [objective matrix](objective-matrix.md) `C`, the
[enumerated multipliers](lifted-multiplier.md) `λ_i` and the [coefficient matrices](lifted-coeff.md)
`A_i`.
