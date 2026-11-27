# Pooled marginal likelihood with a negative binomial total count

For `a > 0`, `b > 0` and a finite set of cells `j` with size factors `sⱼ > 0`, counts `kⱼ ∈ ℕ`,
`K = ∑ⱼ kⱼ` and `S = ∑ⱼ sⱼ`, the [joint marginal likelihood](pooled-marginal-lik.md) is
`Mult(k; K, (sⱼ / S)ⱼ) · NB(K; a, S a / b)`, with the
[multinomial mass](../../../Probability/distributions/discrete/multinomial-distribution/multinomial-real.md)
`Mult(k; K, p) = K! / ∏ⱼ kⱼ! · ∏ⱼ pⱼ^(kⱼ)` and the
[negative binomial mass](../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-real.md)
of the total count with size `a` and mean `S a / b`. With at least one cell, `S > 0` and the weights
`sⱼ / S` form a probability vector on the cells, so the multinomial factor is the probability of the
split `k` of `K` among the cells. With no cells, `S = K = 0`, the weights sum to `0`, not `1`, and
the multinomial factor is `1` for the empty split; the identity still holds.
