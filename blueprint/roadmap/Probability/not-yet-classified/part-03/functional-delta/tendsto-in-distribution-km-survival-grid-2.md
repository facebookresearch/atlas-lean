# Kaplan–Meier limit law on a fixed grid, from the cumulative-hazard CLT

If the
Nelson–Aalen estimates at the grid times satisfy `√n (Λ̂ₙ - Λ) ⇒ G` in `Fin k → ℝ` (sup norm),
then `√n (Ŝₙ - S) ⇒ -duhamelDeriv (-ΔΛ) (ΔG)` with `S = prodIntegral (-ΔΛ)` and
`Δ = gridIncrements`. This is the cumulative-hazard → survival map on the grid.

The CLT is the explicit hypothesis `hCLT`. As in `tendstoInDistribution_kmSurvival_grid`, the
data sets should share the fixed grid times.
