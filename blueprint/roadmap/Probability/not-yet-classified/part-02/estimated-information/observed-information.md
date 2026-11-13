# Observed Information

The **observed information** of a sample `x 0, …, x (n - 1)` at `θ`: minus the average of
the derivatives of the score, `Ĵₙ(θ) = -(1/n) ∑_{i<n} D_θ score p θ (x i)`. When the score is
the gradient of `θ ↦ log p θ x`, this is minus the average Hessian of the log-likelihood. For
`n = 0` it is `0` (Lean's `0⁻¹ = 0`).
