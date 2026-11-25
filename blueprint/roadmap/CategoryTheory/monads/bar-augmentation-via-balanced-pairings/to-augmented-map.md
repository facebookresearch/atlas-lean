# To Augmented Map

Functoriality: given module morphisms `fR : R ⟶ R'`, `fL : L ⟶ L'`,
a target morphism `q : b.target ⟶ b'.target`, and the degree-zero square
`barMap fR fL 0 ≫ b'.pairing = b.pairing ≫ q`, construct the induced map
`b.toAugmented ⟶ b'.toAugmented` in `Data.Augmented (A ⥤ D)`.
Uses the generic uniqueness theorem `Data.hom_eq_of_app_zero_eq`
to prove the comma square; no higher face/degeneracy compatibility is re-proved.
