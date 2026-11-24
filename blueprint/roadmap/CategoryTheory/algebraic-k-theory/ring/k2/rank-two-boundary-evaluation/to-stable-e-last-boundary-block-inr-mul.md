# To Stable E last Boundary Block inr mul inl eq one imp

Rank-two row-times-column forcing: `toStableE (lastBoundaryBlock 1 (inr r) *
lastBoundaryBlock 1 (inl c)) = 1` forces `r = 1` and `c = 1` over a field.
Symmetric to `toStableE_lastBoundaryBlock_one_mul_one_eq_one_imp`; proved by
taking inverses and applying the column-then-row version to `c⁻¹`, `r⁻¹`.
Uses `MonoidHom.map_inv`, `lastBoundaryBlock_inl`/`inr`, and `map_inv` for
`lastColumnProduct`/`lastRowProduct`; does not use private `lastBoundaryBlock_inv`.
Nonclaims: no arbitrary `finiteStage 2` normalization, no rank-two kernel base,
not arbitrary-rank; only `Fin 1`.
