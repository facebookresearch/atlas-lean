# The mean of Tajima's `D` under the neutral model

**The mean of Tajima's `D` under the neutral model** is the covariance of the numerator
`N = π - S / a₁` with the reciprocal denominator `1 / √(e₁ S + e₂ S (S - 1))`, for `n ≥ 4` genes
and integer-valued `S`, under the hypotheses of `KingmanTimes.integral_tajimaNumerator` (which
gives `E[N] = 0`). Whether this covariance vanishes is a property of the joint law of `(π, S)`,
not of the first two moments of `N`; see `exists_integral_tajimaD_ne`.

Under the neutral model `S = 0` has positive probability, and there `D` takes Lean's junk value
`N / √0 = 0` (Tajima's `D` is undefined), so the left side is `E[D; S ≥ 1]`, the mean of `D` over
samples with at least one segregating site, with `D := 0` on `S = 0`.
