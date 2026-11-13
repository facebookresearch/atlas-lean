# Fisher's exact conditional law

Let `X ~ Bin(n₁, p)` and `Y ~ Bin(n₂, p)` be independent
with a common `p ∈ (0, 1)`. Given the margin `X + Y = t` with `t ≤ n₁ + n₂`, the cell `X` is
hypergeometric: `P(X = k | X + Y = t) = C(n₁, k) C(n₂, t - k) / C(n₁ + n₂, t)`, whatever `p`.

## Sources

- Fisher (1934, §21.02; 1935); Lehmann–Romano (2005), §4.5.
