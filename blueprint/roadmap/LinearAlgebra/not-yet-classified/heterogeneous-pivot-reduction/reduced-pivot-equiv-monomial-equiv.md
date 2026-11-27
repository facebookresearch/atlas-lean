# Reduced Pivot Equiv monomial Equiv

After canonical pivot clearing a monomial equivalence, its reduced pivot
equivalence, reindexed along the equality of the canonical pivot row with
`σ canonicalColumn`, is the monomial equivalence built from `deleteWeights`
and `deletePerm`.

Orientation fix: `canonicalPivotRow_monomialEquiv` proves
`canonicalPivotRow (monomialEquiv w σ) = σ canonicalColumn`.  The reindex
needs `DeletedIndex m (σ c) ≃ DeletedIndex m (canonicalPivotRow _)`,
i.e. the symmetric equality, which is `.symm` of the stated helper.
The task statement therefore type-checks with `.symm`; this is the only
adjustment beyond `(R := K)`.

Uses the fixed-point `canonicalPivotCleared_monomialEquiv`, `val_reindex`,
and a direct entrywise argument via `val_monomialEquiv_apply` and
`deletePerm_apply_eq_iff`.  No case split on `Fintype.card n`; the empty
`DeletedIndex` case is uniform because `submatrix` and `monomialEquiv` handle vacuous indices.
