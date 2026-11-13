# Of LV

Lotka–Volterra to replicator coordinates: `x_none = 1 / (1 + ∑ y_j)`,
`x_i = y_i / (1 + ∑ y_j)`. Meaningful for `1 + ∑ y_j ≠ 0`, where it lands in the affine
hyperplane `∑ x_k = 1` (`sum_ofLV`); for positive `y` it lands in the interior of the simplex
(`ofLV_pos`).
