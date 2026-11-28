# Rate root at a fixed shape

For a finite family of counts `k₁, …, kₙ`, real size factors `s₁, …, sₙ` and a real shape `a`, the
rate root `b̂(a)` is a positive root `b` of the
[rate score](../likelihood-equations-and-efficiency-of-the-gamma/rate-score.md) equation
`∑ᵢ (a / b - (a + kᵢ) / (b + sᵢ)) = 0` if there is one (an unspecified one if there are several),
and `0` if there is none. In the rate score `x / 0 = 0`, which matters only if `b + sᵢ = 0` for some
`i`.

On the intended domain, `a > 0`, positive size factors and `n ≥ 1`, the equation has at most one
positive root, and it has one exactly when some count is positive; see
[existence](../likelihood-equations-and-efficiency-of-the-gamma/exists-rate-score-eq-zero.md),
[uniqueness](../likelihood-equations-and-efficiency-of-the-gamma/rate-score-eq-zero-unique.md) and
[no root for all-zero counts](../likelihood-equations-and-efficiency-of-the-gamma/rate-score-pos-of-counts-eq-zero.md).
Then `b̂(a)` is that root ([the rate root solves the equation](rate-root-spec.md)); with all counts
`0`, `b̂(a) = 0`. For an empty family every `b > 0` solves the empty equation, and `b̂(a)` is an
unspecified positive number. At a common size factor `σ > 0` with
[sample mean](../likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M > 0` and
`a > 0`, `b̂(a) = σ a / M` ([common size factor](rate-root-const.md)).
