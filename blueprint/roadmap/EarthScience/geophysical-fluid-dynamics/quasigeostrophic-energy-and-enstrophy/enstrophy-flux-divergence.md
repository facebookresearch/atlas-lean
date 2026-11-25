# The enstrophy flux divergence is q times the Jacobian

For real values `ψ_x`, `ψ_y`, `ψ_xy` of the partial derivatives of a streamfunction `ψ` and
`q`, `q_x`, `q_y` of the potential vorticity, the divergence of the enstrophy flux
`F = (-ψ_y q² / 2, ψ_x q² / 2)`, written out as
`(-ψ_xy q² / 2 - ψ_y q q_x) + (ψ_xy q² / 2 + ψ_x q q_y)`, equals `q J(ψ, q)`, where
`J(ψ, q) = ψ_x q_y - ψ_y q_x`. Hence, under the quasigeostrophic equation `q_t = -J(ψ, q)`,
`∂ₜ(q² / 2) = -q J(ψ, q)` is in divergence form; integrated over a channel it reduces to
boundary terms, which vanish for periodic `x` and walls with `ψ = 0`.
