# Is Row Reduced Conservation

`W` is a **row-reduced conservation matrix** with pivots `piv`: its rows form a basis of
`im(N)^⊥` (they are linearly independent, annihilate every column of `N`, and every vector
orthogonal to all columns of `N` is a combination of them), `piv` is strictly increasing,
`W k (piv k) = 1`, `W k j = 0` for `j < piv k`, and `W k' (piv k) = 0` for `k' ≠ k`.
