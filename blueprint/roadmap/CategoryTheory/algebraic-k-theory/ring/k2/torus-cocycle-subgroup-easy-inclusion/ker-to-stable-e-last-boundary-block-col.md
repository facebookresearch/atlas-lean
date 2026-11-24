# Ker to Stable E last Boundary Block col row pair mem torus Cocycle Subgroup

Column-then-row pair kernel membership for `Fin 1` only.

If `toStableE (lastBoundaryBlock 1 (inl c) * lastBoundaryBlock 1 (inr r)) = 1`,
then the product lies in `torusCocycleSubgroup`. No claim about arbitrary
`Sum` pairs, row-then-column order, `finiteStage 2`, or global normal forms.
Uses `toStableE_lastBoundaryBlock_one_mul_one_eq_one_imp` to force `c = 1`,
`r = 1`, then public block/product hom APIs to reduce to `1`.
