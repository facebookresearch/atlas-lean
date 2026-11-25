# The mean of Tajima's D

Let `π` and `S` be real functions on a probability space and let `n` be a natural number (the
sample size). Write `N = π - S / a₁` for Tajima's numerator and `R = 1 / √(e₁ S + e₂ S (S - 1))`
for the reciprocal of its denominator, so that [Tajima's D](../tajima-s-d/tajima-d.md) is
`D = N R`. As in the definition of `D`, `x / 0 = 0` and `√x = 0` for `x ≤ 0`; in particular
`S / a₁ = 0` for `n ≤ 1`, where `a₁ = 0`, and `R = 0` and `D = 0` wherever
`e₁ S + e₂ S (S - 1) ≤ 0`. If `N` and `R` are in `L²` (nothing is assumed about `π` and `S`
separately, not even measurability), then `E[D] = Cov(N, R) + E[N] E[R]`. Under the neutral model
`E[N] = 0`, so `E[D]` is the
[covariance of the numerator with the reciprocal denominator](integral-tajima-d-eq-covariance.md).
