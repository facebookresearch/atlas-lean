# Stochastic Integral

The **stochastic integral** `(H • M)ₙ = ∑_{k < n} H_{k+1} (M_{k+1} - M_k)` of an integrand `H`
against a process `M` on the time grid `0, 1, 2, …`. The integrand is evaluated at the *right*
end `k + 1` of the step `(k, k + 1]`; it is meant to be predictable (`H (k + 1)` known at time `k`,
Mathlib's `IsStronglyPredictable`), the convention of `Submartingale.sum_mul_sub'`.
