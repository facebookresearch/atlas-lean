# Integral equation of the scaled buck state

Let `L`, `C`, `R`, `Iref` and `Vref` be positive reals, `Vin` and `T ≥ 0` real numbers,
`s, i, v : ℝ → ℝ` functions of time with `s` integrable on `[0, T]` and `i`, `v` continuous on
`[0, T]`, and `i₀`, `v₀` real numbers with `i(t) = i₀ + ∫_0^t (s(u) Vin - v(u)) / L du` and
`v(t) = v₀ + ∫_0^t (i(u) - v(u) / R) / C du` for every `t ∈ [0, T]`. Then for every `t ∈ [0, T]` the
[scaled state](scaled-state.md) `z(t)` of `(i(t), v(t))` satisfies
`z(t) = z₀ + ∫_0^t (Ã z(u) + s(u) b̃) du`, where `z₀` is the scaled state of `(i₀, v₀)`, `Ã` the
[scaled buck operator](scaled-buck-operator.md) and `b̃` the
[scaled input vector](scaled-buck-input.md).
