# Total branch length of a Kingman genealogy from its epoch lengths

For every natural number `n` and all real epoch lengths `t_k` (`2 ≤ k ≤ n`), the
[branch lengths](kingman-branch-length.md) of the Kingman genealogy sum to

`∑_b ℓ_b(t) = ∑_{k=2}^{n} k max(t_k, 0)`,

since epoch `k` has `k` branches of length `max(t_k, 0)`. For nonnegative epoch lengths this is
`∑_{k=2}^{n} k t_k`.
