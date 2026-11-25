# With some score nonzero, the λ̂-corrected statistics sum to m

For real scores `z_0, …, z_{m-1}` that are not all zero (`∑ₖ zₖ² ≠ 0`), the [estimated-factor
statistics](gc-stat.md) `T_j = z_j² / λ̂` of all genes sum to exactly `m`:

`∑ⱼ T_j = m`.

Since every `T_j ≥ 0`, the vector `(T_0, …, T_{m-1})` lies on the simplex of nonnegative vectors
with sum `m`, so a large corrected statistic for one gene forces small ones elsewhere. If all scores
vanish, every `T_j` is `0` by the convention `x / 0 = 0`, and the sum is `0`.
