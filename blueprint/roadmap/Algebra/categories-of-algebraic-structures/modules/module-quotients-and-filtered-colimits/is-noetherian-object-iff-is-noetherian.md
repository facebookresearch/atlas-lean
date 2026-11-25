# Is Noetherian Object iff is Noetherian

A module object in `ModuleCat R` is categorically noetherian iff it is algebraically
noetherian as an `R`-module. The bridge uses `ModuleCat.subobjectModule`, the order
isomorphism `Subobject M ≃o Submodule R M`, and the characterisations
`IsNoetherian R M ↔ WellFoundedGT (Submodule R M)` and
`IsNoetherianObject M ↔ WellFoundedGT (Subobject M)` via strict order well-foundedness.
