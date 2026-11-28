# Heterogeneous Bruhat Decomposition map

Coefficient naturality for the canonical heterogeneous Bruhat decomposition
over division rings. The canonical decomposition commutes with any division-ring
homomorphism `f : K →+* L` on all four components: left upper factor, unit
weights, permutation and right upper factor. The proof is by structural induction
on `Fintype.card m`, using the reusable private nonzero-branch equation
`heterogeneousBruhatDecompositionAux_build`, together with
`leftUpperFactor`/`rightUpperFactor` naturality (`upperRowClear_map`,
`upperColumnClear_map`), `insertWeights`/`insertEquiv` preservation,
`UpperElementary.extendByIdentity` naturality (`upper_extendByIdentity_mapRingHom`),
and the pivot lemmas `canonicalPivotRow_map`, `canonicalPivotUnit_map`,
`reducedPivotEquiv_map_eq`. The empty case follows from `IsEmpty` elimination
for weights and `map_one` for the unipotent factors.
