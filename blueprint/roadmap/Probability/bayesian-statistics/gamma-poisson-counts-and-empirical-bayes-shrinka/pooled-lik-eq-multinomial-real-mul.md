# Factorization of the pooled likelihood

For a finite set of cells `j` with size factors `sⱼ > 0`, counts `kⱼ ∈ ℕ`, `K = ∑ⱼ kⱼ` and
`S = ∑ⱼ sⱼ`, and every real `r`, the [joint likelihood](pooled-lik.md) is
`L(k ∣ r) = Mult(k; K, (sⱼ / S)ⱼ) · e^(−S r) (S r)^K / K!`: the
[multinomial mass](../../../Probability/distributions/discrete/multinomial-distribution/multinomial-real.md)
of the split `k` of `K` with cell probabilities `sⱼ / S`, which does not depend on the rate, times
the [Poisson likelihood](poisson-exposure-lik.md) of `K` at exposure `S`.

## Sources

- W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed., Wiley
  (1968), §VI.9.
