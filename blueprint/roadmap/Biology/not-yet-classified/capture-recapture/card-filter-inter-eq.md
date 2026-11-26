# The recapture count is hypergeometric

Let a population `Fin N` contain a
marked set `A` of size `n₁`, and let the second sample be a uniformly random subset of size
`n₂ ≤ N`. For every `k : ℕ`, the proportion of `n₂`-subsets `S` with `#(S ∩ A) = k` equals
`hypergeometricReal N n₁ n₂ k`, which is `C(n₁, k) C(N - n₁, n₂ - k) / C(N, n₂)` for `k ≤ n₂` and
`0` for `k > n₂` (note that for `k > n₂`, natural-number subtraction would make the unguarded
binomial quotient nonzero, whereas `hypergeometricReal` is zero outside `k ≤ n₂`).

## Sources

- D. G. Chapman, "Some properties of the hypergeometric distribution with applications to zoological sample censuses", Univ. California Publ. Statist. 1 (1951) 131–160.
