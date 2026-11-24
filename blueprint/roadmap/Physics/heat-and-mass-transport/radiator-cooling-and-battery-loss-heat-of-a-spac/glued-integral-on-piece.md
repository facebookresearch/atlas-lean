# Integral form of a glued radiator temperature on each piece

Let `C > 0` and `K_rad` be real numbers, `m` a natural number, `τ : ℕ → ℝ` strictly increasing
switch times, `Q : ℕ → ℝ` heat inputs per mode and `T : ℝ → ℝ` a temperature such that, for every
`j < m`, `T` is continuous on `[τ_j, τ_{j+1}]` and has derivative `(Q_j - K_rad T(t)⁴) / C` at
every `t ∈ (τ_j, τ_{j+1})`. Then for every `j < m` and every `t ∈ [τ_j, τ_{j+1}]`,

`T(t) - T(τ_j) = ∫_{τ_j}^t (Q_j - K_rad T(s)⁴) / C ds`.
