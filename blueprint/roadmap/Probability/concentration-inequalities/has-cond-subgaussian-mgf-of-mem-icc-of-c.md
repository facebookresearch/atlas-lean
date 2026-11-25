# Conditional Hoeffding lemma

Let `μ` be a finite measure on a standard Borel space and `m`
a sub-σ-algebra. If an almost everywhere measurable real random variable `X` takes values in
`[a, b]` almost everywhere and its conditional expectation `μ[X | m]` given `m` vanishes almost
everywhere, then `X` is conditionally sub-Gaussian given `m` with parameter `((b - a) / 2) ^ 2`:
`exp (t * X)` is integrable for every real `t`, and for almost every point with respect to the
restriction of `μ` to `m`, the moment-generating function of `X` under the conditional
distribution given `m` at that point is at most `exp ((b - a) ^ 2 * t ^ 2 / 8)` for every real
`t`.
