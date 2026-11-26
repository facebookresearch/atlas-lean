# Error bound between switched and averaged scaled buck states

Let `L`, `C`, `R`, `Iref` and `Vref` be positive reals, `Vin` real, `T ≥ 0`, `ε > 0`, `Ld ≥ 0`, and
`d : ℝ → ℝ` a duty with values in `[0, 1]` on `[0, T]` that is `Ld`-Lipschitz on `[0, T]`. Let `s_ε`
be the pulse-width signal of cycle length `ε`: on the cycle `[k ε, (k + 1) ε)` it is `1` on
`[k ε, k ε + d(k ε) ε)` and `0` on the rest. Suppose `i`, `v`, `ī` and `v̄` are continuous on
`[0, T]` and satisfy, for every `t ∈ [0, T]`, the switched equations
`i(t) = i₀ + ∫_0^t (s_ε(u) Vin - v(u)) / L du`, `v(t) = v₀ + ∫_0^t (i(u) - v(u) / R) / C du` and the
averaged equations `ī(t) = ī₀ + ∫_0^t (d(u) Vin - v̄(u)) / L du`,
`v̄(t) = v̄₀ + ∫_0^t (ī(u) - v̄(u) / R) / C du`. Then for every `t ∈ [0, T]` the
[scaled states](scaled-state.md) `z(t)` of `(i(t), v(t))` and `z̄(t)` of `(ī(t), v̄(t))`, with `z₀`
and `z̄₀` those of `(i₀, v₀)` and `(ī₀, v̄₀)`, satisfy
`‖z(t) - z̄(t)‖ ≤ exp(‖Ã‖ T) (‖z₀ - z̄₀‖ + ‖b̃‖ ε (1 + Ld T / 2))`, with the maximum norm, the
operator norm of the [scaled buck operator](scaled-buck-operator.md) `Ã` and the
[scaled input vector](scaled-buck-input.md) `b̃`.
