# Factorization of the pooled likelihood

For a finite set of cells `j` with size factors `sⱼ > 0`, counts `kⱼ ∈ ℕ`, `K = ∑ⱼ kⱼ` and
`S = ∑ⱼ sⱼ`, and every real `r`, the [joint likelihood](pooled-lik.md) is

`L(k ∣ r) = Mult(k; K, (sⱼ / S)ⱼ) · e^(−S r) (S r)^K / K!`,

where `Mult(k; K, p) = K! / ∏ⱼ kⱼ! · ∏ⱼ pⱼ^(kⱼ)` is the
[multinomial mass](../../distributions/discrete/multinomial-distribution/multinomial-real.md),
so the first factor does not depend on the rate, and the second factor is the
[Poisson likelihood](poisson-exposure-lik.md) of `K` at exposure `S`. With at least one cell,
`S > 0`, the weights `sⱼ / S` form a probability vector on the cells and the first factor is the
probability of the split `k` of `K` among the cells, while the second factor is the mass of `K`
under the Poisson law `Po(S r)` for `r ≥ 0`, that is, when `S r ≥ 0`; for `r < 0` it is only the
formula. With no cells, `S = K = 0`, the weights sum to `0`, not `1`, and both factors and the
likelihood equal `1`; the identity still holds.

## Sources

- W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed., Wiley
  (1968), §VI.9.
