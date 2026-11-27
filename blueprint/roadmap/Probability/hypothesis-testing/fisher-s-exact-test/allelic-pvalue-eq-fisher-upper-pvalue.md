# Allelic p-value as Fisher's p-value at the observed margin

For natural numbers `n₁`, `n₂` and `t` with `t ≤ n₁ + n₂`, allele counts `X, Y : Ω → ℕ` and an
outcome `ω` with `X ω + Y ω = t`, the [allelic p-value](allelic-pvalue.md) at `ω` equals the
[upper Fisher exact p-value](fisher-upper-pvalue.md)
of `X` at `ω` with group sizes `n₁`, `n₂` and margin `t`: on this event the cap on the margin is
inactive.
