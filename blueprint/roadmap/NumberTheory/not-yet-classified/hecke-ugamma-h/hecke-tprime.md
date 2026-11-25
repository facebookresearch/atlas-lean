# Hecke TPrime

The prime-index Hecke formula `T_p f = U_p f + f ∣[k] diag(p, 1)`, that is,
`(p : ℂ)⁻¹ * ∑ j < p, f ((τ + j) / p) + p ^ (k - 1) * f (p * τ)` (see `heckeTPrime_apply`).
It is stated only for a prime `p`: at a composite index the Hecke operator has further divisor
terms, so this two-term formula is not `T_n` in general.
