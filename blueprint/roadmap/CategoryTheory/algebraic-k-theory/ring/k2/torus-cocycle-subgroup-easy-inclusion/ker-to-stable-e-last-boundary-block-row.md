# Ker to Stable E last Boundary Block row col pair mem torus Cocycle Subgroup

Row-then-column pair kernel membership for `Fin 1` only.

If `toStableE (lastBoundaryBlock 1 (inr r) * lastBoundaryBlock 1 (inl c)) = 1`,
then the product lies in `torusCocycleSubgroup`. No claim about arbitrary
`Sum` pairs, arbitrary `finiteStage 2` normalization, or the rank-two kernel
base. Uses `toStableE_lastBoundaryBlock_inr_mul_inl_eq_one_imp` to force
`r = 1`, `c = 1`, then public block/product hom APIs to reduce to `1`.
