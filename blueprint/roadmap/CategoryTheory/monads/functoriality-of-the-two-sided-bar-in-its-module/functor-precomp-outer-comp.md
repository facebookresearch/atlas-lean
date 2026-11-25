# Functor Precomp Outer Comp

Composition coherence for the outer source precomposition functor.

For `H : B ⥤ A` and `J : B₂ ⥤ B`, this is the appropriately oriented
`(Functor.whiskeringLeftObjCompIso J H).symm` (which is `Iso.refl _.symm`),
preserving the contravariant orientation
`precomp H ⋙ precomp J ≅ precomp (J ⋙ H)`.
The reversed-associator description follows since all components are identities.
No pseudofunctor is built.
