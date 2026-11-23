# One-sided exact allelic p-value of a case–control variant

For natural numbers `n₁` and `n₂`, the numbers of case and control alleles, and allele counts
`X, Y : Ω → ℕ`, the numbers of copies of the tested allele among the case and the control alleles,
the one-sided exact allelic p-value at an outcome `ω` is the
[upper Fisher exact p-value](fisher-upper-pvalue.md)
of `X` with group sizes `n₁`, `n₂` and margin `t = min(X ω + Y ω, n₁ + n₂)`: the probability
`H{j ≥ X ω}` of a count at least `X ω` under the
[hypergeometric law](../../distributions/discrete/hypergeometric-distribution/hypergeometric.md)
`H = H(n₁ + n₂, n₁, t)`. The margin is capped at `n₁ + n₂` so that the definition is total. When
`X ω ≤ n₁` and `Y ω ≤ n₂`, which holds almost surely under the binomial null of the
[validity theorem](is-valid-pvalue-allelic-pvalue.md), the cap changes nothing. Otherwise the value
can be degenerate: it is `0` when `X ω > n₁`, and when `X ω + Y ω > n₁ + n₂` the capped margin makes
`H` the point mass at `n₁`, so the value is `1` if `X ω ≤ n₁`.
