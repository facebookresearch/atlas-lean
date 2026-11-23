# Pooled marginal likelihood as a multinomial split of the total count

For real numbers `a` and `b` and a finite set of cells `j` with size factors `sⱼ > 0`, counts
`kⱼ ∈ ℕ`, `K = ∑ⱼ kⱼ` and `S = ∑ⱼ sⱼ`, the [joint marginal likelihood](pooled-marginal-lik.md) is
`Mult(k; K, (sⱼ / S)ⱼ) · m_S(K)`, the
[multinomial mass](../../../Probability/distributions/discrete/multinomial-distribution/multinomial-real.md)
of the split `k` of `K` with cell probabilities `sⱼ / S` times the
[marginal likelihood](marginal-lik.md) `m_S(K)` of the count `K` at exposure `S`. No sign condition
on `a` or `b` is needed, since the multinomial factor does not depend on the rate.
