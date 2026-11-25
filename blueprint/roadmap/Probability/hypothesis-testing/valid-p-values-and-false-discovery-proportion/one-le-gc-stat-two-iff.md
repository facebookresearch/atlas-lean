# With two genes and a nonzero score vector, T₀ ≥ 1 iff z₁² ≤ z₀²

For two genes with real scores `z_0, z_1` that are not both zero (`z_0² + z_1² ≠ 0`), the
[estimated-factor statistic](gc-stat.md) of gene `0` satisfies

`T_0 ≥ 1` if and only if `z_1² ≤ z_0²`, and `T_0 < 1` if and only if `z_0² < z_1²`.

If both scores are zero, `T_0 = 0 < 1` by the convention `x / 0 = 0`, although `z_1² ≤ z_0²`.
