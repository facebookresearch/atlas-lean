# Pooled marginal likelihood with a negative binomial total count

For `a > 0`, `b > 0` and a finite set of cells `j` with size factors `sⱼ > 0`, counts `kⱼ ∈ ℕ`,
`K = ∑ⱼ kⱼ` and `S = ∑ⱼ sⱼ`, the [joint marginal likelihood](pooled-marginal-lik.md) is
`Mult(k; K, (sⱼ / S)ⱼ) · NB(K; a, S a / b)`: the
[multinomial mass](../../../Probability/distributions/discrete/multinomial-distribution/multinomial-real.md)
of the split `k` of `K` with cell probabilities `sⱼ / S` times the
[negative binomial mass](../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-real.md)
of the total count with size `a` and mean `S a / b`.
