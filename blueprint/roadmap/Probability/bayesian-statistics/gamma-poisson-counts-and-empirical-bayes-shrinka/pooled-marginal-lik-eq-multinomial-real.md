# Pooled marginal likelihood as a multinomial split of the total count

For real numbers `a` and `b` and a finite set of cells `j` with size factors `sⱼ > 0`, counts
`kⱼ ∈ ℕ`, `K = ∑ⱼ kⱼ` and `S = ∑ⱼ sⱼ`, the [joint marginal likelihood](pooled-marginal-lik.md) is
`Mult(k; K, (sⱼ / S)ⱼ) · m_S(K)`, with the
[multinomial mass](../../distributions/discrete/multinomial-distribution/multinomial-real.md)
`Mult(k; K, p) = K! / ∏ⱼ kⱼ! · ∏ⱼ pⱼ^(kⱼ)` and the [marginal likelihood](marginal-lik.md) `m_S(K)`
of the count `K` at exposure `S`. No sign condition on `a` or `b` is needed, since the multinomial
factor does not depend on the rate. With at least one cell, `S > 0` and the weights `sⱼ / S` form a
probability vector on the cells, so the multinomial factor is the probability of the split `k` of
`K` among the cells. With no cells, `S = K = 0`, the weights sum to `0`, not `1`, and the
multinomial factor is `1` for the empty split; the identity still holds.
