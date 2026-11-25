# To Stable E torus fin last prod eq reindex product One Diagonal

Finite product of boundary torus images equals the
`fromFinite (n+1)` image of the product-one diagonal reindexed by
`finSumFinEquiv (m := n) (n := 1)`.

Orientation: `∏ i, toStableE (torus i.val n _ (u i)) =
fromFinite F (n+1) (reindex finSumFinEquiv (diagonalUnitsHom
(productOneDiagonal u)))`.

Uniform for `n = 0` (empty product is `1`) and valid in
characteristic two. This holds only after `toStableE`; it does not
claim exact torus multiplication in `StableSteinberg`, whose defect is
central.
