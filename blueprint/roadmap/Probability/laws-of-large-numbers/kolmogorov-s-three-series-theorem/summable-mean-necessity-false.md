# The `Summable`-means necessity claim in v1 is false

The
deterministic sequence `X k ω = (-1)^k / (k + 1)` on the one-point
probability space `(Unit, dirac ())` has converging partial sums, is
constant (hence measurable and independent), agrees with its truncations
at `A = 1`, and has all variances `0` — yet its means
`∫ truncatedRV X 1 k = (-1)^k / (k + 1)` are not `Summable`, since
`Summable.abs` would force summability of the harmonic series. This is
why the ported necessity theorem above states convergence of the mean
partial sums rather than `Summable` of the means. The statement records
convergence of both the original and the truncated partial sums: the
truncated form is the hypothesis of v1's (false) unproved lemma, and the original
form is what the corrected assembly theorem needs.
