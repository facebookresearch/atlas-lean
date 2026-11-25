# The aggregate and an index are jointly Gaussian

Let `μ` be a measure on `Ω` and `M` a
Smith–Hazel model on `n` traits under `μ` whose additive values and residuals `(A, E)` are
jointly Gaussian under `μ` (`HasGaussianLaw (fun ω => (M.additive ω, M.residual ω)) μ`). Then for
every coefficient vector `b`, the pair `(M.aggregate, M.index b)` is jointly Gaussian under `μ`.
