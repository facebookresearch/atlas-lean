# The certified bound in enumerated constraint form

For every
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md)
`P` (a network with branch and shunt admittances, fixed demands, generation limits, squared
voltage-magnitude bounds, squared branch-current limits and linear active-generation cost
coefficients `c_k`) and [AC dual witness](acdual-certificate.md), the
[certified lower bound](certified-lower-bound.md) `L` equals `c₀ - Σ_i λ_i b_i`, with the
[constant term](objective-offset.md) `c₀`, the [enumerated multipliers](lifted-multiplier.md) `λ_i`
and the [right-hand sides](lifted-bound.md) `b_i`.
