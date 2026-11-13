# Monotone likelihood ratio

The likelihood family `L : ℕ → ℝ → ℝ` (observation, parameter) has a **monotone
likelihood ratio** on the parameter set `S`: `L` is nonnegative on `S`, and for
observations `n ≤ m` and parameters `θ ≤ θ'` in `S`,
`L m θ * L n θ' ≤ L n θ * L m θ'` (total positivity of order two). For positive
likelihoods this is monotonicity of `θ ↦ L m θ / L n θ`. The nonnegativity is part of
the predicate: without it the downstream `posteriorTail` would not be a posterior
probability (a signed `L` can give `posteriorTail > 1`).
