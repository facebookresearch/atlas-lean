# Error bound between switched and averaged buck trajectories

Under the hypotheses of the [scaled-state bound](scaled-state-switched-averaged-error-le.md)
(positive `L`, `C`, `R`, `Iref`, `Vref`; `T ≥ 0`, `ε > 0`; a duty `d` with values in `[0, 1]` that
is `Ld`-Lipschitz on `[0, T]`; continuous switched and averaged trajectories satisfying their
integral equations on `[0, T]`), for every `t ∈ [0, T]`, `|i(t) - ī(t)| ≤ Iref B` and
`|v(t) - v̄(t)| ≤ Vref B`, where `B` is the [error bound](scaled-buck-error-bound.md) at
`Δi₀ = i₀ - ī₀` and `Δv₀ = v₀ - v̄₀`:
`B = exp(κ T) (max(|Δi₀| / Iref, |Δv₀| / Vref) + |Vin| / (L Iref) · ε (1 + Ld T / 2))`.
