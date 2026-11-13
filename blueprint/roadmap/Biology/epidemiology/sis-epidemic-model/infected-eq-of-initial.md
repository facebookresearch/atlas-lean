# Forward uniqueness of the infectives

Two solutions with the same population
`S(0) + I(0) = N ≠ 0` and the same `I(0)` have the same `I` on `[0, ∞)`.

Proof: both `I`s solve the scalar equation `x' = (β - γ) x - (β / N) x²`
(`hasDerivAt_infected_logistic`); on `[0, t]` they are bounded, and the polynomial field is
Lipschitz on a closed ball containing both; apply `ODE_solution_unique_of_mem_Icc_right`.
