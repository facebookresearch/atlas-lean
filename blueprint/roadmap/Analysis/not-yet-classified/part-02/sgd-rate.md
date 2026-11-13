# Projected Subgradient

The `D G / √T` rate of the projected subgradient method: for a
convex objective with subgradients bounded by `G` (the subgradient
inequality quantified over every comparison point `y`), a
nonexpansive projection fixing `xstar`, and `‖x0 - xstar‖ ≤ D`, the
average `x̄` of `x₀, …, x_{T-1}` with step `η = D / (G √T)`
(so `x̄ = x0` when `T = 1`)
satisfies `f x̄ - f xstar ≤ D G / √T`. The summed objective bound is
`ogd_regret` at the constant round cost `fun _ => f`, with the
subgradient inequality specialized to `xstar`.
