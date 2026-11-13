# Fixed-grid joint central limit theorem for the Aalen–Johansen and Kaplan–Meier estimators under independent censoring

**Fixed-grid joint central limit theorem for the Aalen–Johansen and Kaplan–Meier estimators
under independent censoring.** Let the subjects `Wᵢ = ((Tᵢ, Jᵢ), Cᵢ)` be i.i.d. with law
`indepCauseLaw pTJ pC`, in which the event time and cause `(T, J)` are jointly independent of the
censoring time `C`, and let `P(min T C ≥ m) ≠ 0`. Then
`√n · (Ŝ(j) - P(T > j), F̂_c(j) - P(T ≤ j, J = c))_{c, j ≤ m}` converges in distribution to a
centered Gaussian vector `Y` whose covariance matrix is that of the influence vector of one
subject (`covariance_limit`). Grid times only; no process convergence in `D[0, τ]`.
