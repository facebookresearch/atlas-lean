# Convergence under a fair schedule

Let `T` be a symmetric weight matrix (`Matrix.IsSymm T`)
and `U` any thresholds, and let `σ` be a fair schedule (every neuron is attempted arbitrarily late,
`Fair σ`). Then for every initial state `v₀` there is `K` such that `trajectory T U σ v₀ K` is
stable and `trajectory T U σ v₀ k = trajectory T U σ v₀ K` for every `k ≥ K`.
