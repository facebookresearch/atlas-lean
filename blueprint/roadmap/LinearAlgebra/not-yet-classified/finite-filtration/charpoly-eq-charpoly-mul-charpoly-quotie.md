# Charpoly eq charpoly mul charpoly quotient Map

Characteristic-polynomial factorization for one invariant extension.

This is the reusable one-step block-triangular formula, the
characteristic-polynomial analogue of
`LinearMap.InvariantExtension.det_eq_det_mul_det_quotientMap`.  The upper
stage is assumed free because `LinearMap.charpoly`, unlike `LinearMap.det`,
is only defined on finite free modules.
