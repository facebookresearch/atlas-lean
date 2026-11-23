# Covariance with the case indicator under case-control sampling

Let `μ` be a probability measure on `Ω`, let `L` be a measurable real function on `Ω`, let `t` be a
real threshold such that the cases `C = {t ≤ L}` satisfy `0 < μ(C) < 1`, and let `0 ≤ P ≤ 1`. Write
`k = μ(C)` and `Y = 1{L ≥ t}` for the [case indicator](case-ind.md). Then for every real function
`S` that is square integrable under `μ`,

`Cov_cc(S, Y) = P (1 - P) / (k (1 - k)) · Cov(S, Y)`,

where `Cov_cc` is the covariance under the [case-control law](case-control.md) `μ_cc` with case
fraction `P` and `Cov` the covariance under `μ`. No Gaussian assumption is made. For a liability
with the standard normal law, `k` is the [prevalence](measure-real-case.md) `K(t)`.
