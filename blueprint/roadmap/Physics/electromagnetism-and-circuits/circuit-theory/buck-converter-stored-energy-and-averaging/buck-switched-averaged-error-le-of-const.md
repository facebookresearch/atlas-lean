# Error bound of buck averaging with a constant duty

Let `L`, `C`, `R`, `Iref` and `Vref` be positive reals, `Vin` real, `T ≥ 0` and `ε > 0`. Let `s_ε`
be the pulse-width signal of cycle length `ε` and constant duty `D ∈ [0, 1]`: on every cycle
`[k ε, (k + 1) ε)` it is `1` on `[k ε, k ε + D ε)` and `0` on the rest. Suppose `i`, `v`, `ī` and
`v̄` are continuous on `[0, T]` and satisfy, for every `t ∈ [0, T]`, the switched equations
`i(t) = i₀ + ∫_0^t (s_ε(u) Vin - v(u)) / L du`, `v(t) = v₀ + ∫_0^t (i(u) - v(u) / R) / C du` and the
averaged equations `ī(t) = ī₀ + ∫_0^t (D Vin - v̄(u)) / L du`,
`v̄(t) = v̄₀ + ∫_0^t (ī(u) - v̄(u) / R) / C du`. Then for every `t ∈ [0, T]`,
`|i(t) - ī(t)| ≤ Iref B_D` and `|v(t) - v̄(t)| ≤ Vref B_D` with
`B_D = exp(κ T) (max(|i₀ - ī₀| / Iref, |v₀ - v̄₀| / Vref) + |Vin| / (L Iref) · D (1 - D) ε)`, where
`κ` is the [growth-rate bound](scaled-buck-growth-rate.md). The ripple term vanishes for `D = 0` and
`D = 1`, where the pulse-width signal equals the duty.
