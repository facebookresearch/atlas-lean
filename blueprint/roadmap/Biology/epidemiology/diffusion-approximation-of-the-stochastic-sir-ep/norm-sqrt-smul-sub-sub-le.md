# Kurtz's pathwise estimate for the fluctuations

Let `x` solve `x(t) = x(0) + ∫₀ᵗ F(x)`
on `[0, T]` with `‖x‖ ≤ B`, let `X` be a measurable path with `‖X - x‖ ≤ δ ≤ 1` on `[0, T]`,
and let `U` solve the fluctuation equation driven by `m` from `u₀`, with `‖u₀‖, ‖m‖ ≤ k`. If the
initial fluctuation `√N (X(0) - x(0))` is within `ρ` of `u₀` and the scaled martingale
`√N (X(t) - X(0) - ∫₀ᵗ F(X))` is within `ρ` of `m(t)` on `[0, T]`, then on `[0, T]`

`‖√N (X(t) - x(t)) - U(t)‖ ≤ (3 ρ + β δ T · 3 k e^{L T}) e^{(L + β) T}`,  `L = 2 β B + γ`.

The scaled martingale vanishes at `t = 0`, so `‖m(0)‖ ≤ ρ`; this third `ρ` and the `3 k` of
`IsFluctuationPath.norm_le` come from the increment `m(t) - m(0)` in the fluctuation equation.
The proof writes `√N (F(X) - F(x)) = DF(x) U_N + β (U_N)₁ (X - x)₂ (-1, 1)` (`drift_add`) and
applies Gronwall's inequality to `‖U_N - U‖`.
