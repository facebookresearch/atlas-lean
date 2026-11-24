# Battery heat as a heat input of the eclipse-mode gluing

Let `C > 0`, `m` a natural number, `τ` strictly increasing switch times, heat inputs `Q_env` and
battery powers `P_c`, `P_d` per mode, efficiencies `η_c`, `η_d`, and `T : ℝ → ℝ` continuous on every
`[τ_j, τ_{j+1}]` (`j < m`) with derivative `(Q_env,j + q_j - K_rad T(t)⁴) / C` at every
`t ∈ (τ_j, τ_{j+1})`, where `q_j` is the [battery loss heat](battery-loss-heat.md) of mode `j`.
Then `T` is continuous on `[τ₀, τ_m]` and, for every `j < m` and `t ∈ [τ_j, τ_{j+1}]`,

`T(t) - T(τ_j) = ∫_{τ_j}^t (Q_env,j + q_j - K_rad T(s)⁴) / C ds`.
