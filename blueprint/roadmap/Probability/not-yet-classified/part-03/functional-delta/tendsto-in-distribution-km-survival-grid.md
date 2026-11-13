# Kaplan–Meier limit law on a fixed grid

For any sequence of random grouped censored
data sets `Dn n` (for instance `SurvivalConsistency.empiricalData` on the grid `0, …, k - 1`), if
the Nelson–Aalen increments satisfy `√n (ΔΛ̂ₙ - λ) ⇒ G` in `Fin k → ℝ` (sup norm), then the
Kaplan–Meier estimates at the grid times satisfy
`√n (Ŝₙ - S) ⇒ -duhamelDeriv (-λ) G`, where `S = prodIntegral (-λ)`; coordinatewise the limit is
`-∑_{i ≤ j} S(t_{i-1}) G i ∏_{i < l ≤ j} (1 - λ l)`.

The CLT is the explicit hypothesis `hCLT`. The estimates are evaluated at `(Dn n ω).time j`;
for the statement to be about a fixed grid, the data sets should share the grid times (as
`empiricalData` does).
