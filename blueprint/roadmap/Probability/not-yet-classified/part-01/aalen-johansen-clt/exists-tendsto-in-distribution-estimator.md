# Fixed-grid joint central limit theorem for Kaplan–Meier and Aalen–Johansen

Let the
subjects `Wᵢ = ((Tᵢ, Jᵢ), Cᵢ)` be i.i.d. with law `μ` on `(Fin k × Fin r) × Fin k` (no
independence between `(T, J)` and `C` is assumed here), and let the observed at-risk mass at the
horizon be positive, `P(min T C ≥ m) ≠ 0`. Then the joint vector of the Kaplan–Meier survival
and all `r` Aalen–Johansen cumulative incidences at every grid index `j ≤ m`, centered at its
plug-in limit `ajMap m (cellMean μ)` and scaled by `√n`, converges in distribution to
`L (A z)`, where `L` is the derivative of the Aalen–Johansen map at the mean cell vector and
`A z` is the Gaussian limit of the cell-count central limit theorem
(`exists_tendstoInDistribution_empiricalMean`). The covariance of the limit is identified in
`tendstoInDistribution_estimator` and `covariance_limit`. Grid times only: no process
convergence in `D[0, τ]` is claimed.
