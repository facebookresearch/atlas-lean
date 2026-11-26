# Three-phase complex power is three times the sum of sequence powers

For all complex `V_a`, `V_b`, `V_c`, `I_a`, `I_b`, `I_c`,

`V_a conj(I_a) + V_b conj(I_b) + V_c conj(I_c) = 3 (V₀ conj(I₀) + V₁ conj(I₁) + V₂ conj(I₂))`,

where `V₀`, `V₁`, `V₂` and `I₀`, `I₁`, `I₂` are the [zero](zero-sequence.md),
[positive](positive-sequence.md) and [negative](negative-sequence.md) sequence components of
`(V_a, V_b, V_c)` and of `(I_a, I_b, I_c)`. With voltages and currents as RMS phasors, the left side
is the total complex power absorbed by the three phases (passive sign convention).

With the [phase arrays](phase-vector.md) `v`, `i` and the [sequence arrays](sequence-vector.md)
`v_s`, `i_s` of the voltages and currents, the identity reads
`Σ_p v(p) conj(i(p)) = 3 Σ_s v_s(s) conj(i_s(s))`, both sums over the integers modulo 3.
