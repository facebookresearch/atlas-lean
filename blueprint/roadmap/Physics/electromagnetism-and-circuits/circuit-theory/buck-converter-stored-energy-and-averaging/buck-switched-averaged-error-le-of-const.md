# Error bound of buck averaging with a constant duty

Under the hypotheses of the [averaging bound](buck-switched-averaged-error-le.md) with a constant
duty `D ∈ [0, 1]` (so the pulse-width signal has duty `D` on every cycle and the averaged input is
`D Vin`), for every `t ∈ [0, T]`, `|i(t) - ī(t)| ≤ Iref B_D` and `|v(t) - v̄(t)| ≤ Vref B_D` with
`B_D = exp(κ T) (max(|i₀ - ī₀| / Iref, |v₀ - v̄₀| / Vref) + |Vin| / (L Iref) · D (1 - D) ε)`, where
`κ` is the [growth rate](scaled-buck-growth-rate.md). The ripple term vanishes for `D = 0` and
`D = 1`, where the pulse-width signal equals the duty.
