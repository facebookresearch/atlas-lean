# Replacing one step by every pair of lineages in a sum over histories

For every real function `F` on the [ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes and every step `i < n - 1`,

`(∑_h F(h)) · C(n - i, 2) = ∑_h ∑_x F(h[i ↦ x])`,

where `h` runs over all histories, `x` over the `C(n - i, 2)` [pairs](../ranked-labeled-histories-of-coalescent-trees/lineage-pair.md) of the `n - i` lineages at
step `i`, and `h[i ↦ x]` is `h` with step `i` replaced by `x`. Summing `F` over all histories
`C(n - i, 2)` times is thus summing it over all histories with step `i` replaced by every
possible pair.
