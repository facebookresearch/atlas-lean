# A glued radiator temperature stays in a box mode by mode

Let `C`, `K_rad` be real numbers, `m` a natural number, `τ : ℕ → ℝ` strictly increasing switch
times, `Q : ℕ → ℝ` heat inputs per mode and `T : ℝ → ℝ` a temperature such that, for every `j < m`,
`T` is continuous on `[τ_j, τ_{j+1}]` and has derivative `(Q_j - K_rad T(t)⁴) / C` at every
`t ∈ (τ_j, τ_{j+1})`. Suppose that for every `j < m`, if `T(τ_j) ∈ [T_min, T_max]` then
`T(t) ∈ [T_min, T_max]` for every `t ∈ [τ_j, τ_{j+1}]` (single-mode trapping, supplied as a
hypothesis), and that `T(τ₀) ∈ [T_min, T_max]`. Then `T(t) ∈ [T_min, T_max]` for every
`t ∈ [τ₀, τ_m]`.
