# Finite-horizon dose budget

Let `m` dose events have times `τ_i > 0` and sizes `d_i` (`i < m`), let `k`, `A₀` and `T` be real,
and let the amount `A` satisfy, for every real `t`, the integral equation
`A(t) = A₀ + ∑_{i < m, τ_i ≤ t} d_i - k * ∫₀ᵗ A(s) ds`. Then
`A(T) - A(0) = ∑_{i < m, τ_i ≤ T} d_i - k * ∫₀ᵀ A(s) ds`: on `[0, T]` the change in amount is the
included dose sum minus `k` times the integrated amount, the integral being oriented for `T < 0`.
The initial amount is not counted as a dose: the events counted lie in `(0, T]`.
