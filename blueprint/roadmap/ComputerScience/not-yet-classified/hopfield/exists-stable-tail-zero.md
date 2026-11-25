# Convergence under a fair schedule at zero threshold

**Convergence under a fair schedule at zero threshold** (Hopfield 1982). Let `T` be a symmetric
weight matrix (`Matrix.IsSymm T`), and let `σ` be a fair schedule (`Fair σ`). Then for every initial
state `v₀` there is `K` such that `trajectory T 0 σ v₀ K` is stable for the zero-threshold dynamics
and `trajectory T 0 σ v₀ k = trajectory T 0 σ v₀ K` for every `k ≥ K`.
