# Error bound between switched and averaged buck trajectories

Let `L`, `C`, `R`, `Iref` and `Vref` be positive reals, `Vin` real, `T ≥ 0` and `ε > 0`. Let `s_ε`
be the pulse-width signal of cycle length `ε` and duty `d`, where `d : ℝ → ℝ` has values in `[0, 1]`
on `[0, T]` and is `Ld`-Lipschitz there (`Ld ≥ 0`): on the cycle `[k ε, (k + 1) ε)` it is `1` on
`[k ε, k ε + d(k ε) ε)` and `0` on the rest. Suppose `i`, `v`, `ī` and `v̄` are continuous on
`[0, T]` and satisfy, for every `t ∈ [0, T]`, the switched equations
`i(t) = i₀ + ∫_0^t (s_ε(u) Vin - v(u)) / L du`, `v(t) = v₀ + ∫_0^t (i(u) - v(u) / R) / C du` and the
averaged equations `ī(t) = ī₀ + ∫_0^t (d(u) Vin - v̄(u)) / L du`,
`v̄(t) = v̄₀ + ∫_0^t (ī(u) - v̄(u) / R) / C du` (as in the
[scaled-state bound](scaled-state-switched-averaged-error-le.md)). Then for every `t ∈ [0, T]`,
`|i(t) - ī(t)| ≤ Iref B` and `|v(t) - v̄(t)| ≤ Vref B`, where `B` is the
[error bound](scaled-buck-error-bound.md) at `Δi₀ = i₀ - ī₀` and `Δv₀ = v₀ - v̄₀`:
`B = exp(κ T) (max(|Δi₀| / Iref, |Δv₀| / Vref) + |Vin| / (L Iref) · ε (1 + Ld T / 2))`.
