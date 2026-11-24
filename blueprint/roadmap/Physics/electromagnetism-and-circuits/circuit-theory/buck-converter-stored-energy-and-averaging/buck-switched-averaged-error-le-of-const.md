# Buck switched averaged error le of const Duty

Fixed duty `D ∈ [0, 1]`: the ripple term reduces to
`|Vin| / (L Iref) * (D (1 - D) ε)`, which vanishes at `D = 0` and
`D = 1`, where the pulse-width signal equals the duty.
