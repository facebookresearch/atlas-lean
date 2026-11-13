# Prod Integral

The **product integral on a fixed grid**: for hazard increments `x i` at the grid points
`t₀ < ⋯ < t_{k-1}`, `prodIntegral x j = ∏_{i ≤ j} (1 + x i)`, the product integral
`∏_{(0, t_j]} (1 + dA)` of the pure-jump function `A` with jumps `x i` at `tᵢ`. With
`x = -ΔΛ` it is the survival function of the cumulative hazard `Λ`
(see `kmSurvival_time_eq_prodIntegral`).
