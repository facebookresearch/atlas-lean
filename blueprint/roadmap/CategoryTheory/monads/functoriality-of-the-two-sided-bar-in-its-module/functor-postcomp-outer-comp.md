# Functor Postcomp Outer Comp

Composition coherence for the outer target postcomposition functor.

Direct use of Mathlib's `whiskeringRightObjCompIso` (which is `Iso.refl _`),
preserving the orientation `postcomp K ⋙ postcomp Q ≅ postcomp (K ⋙ Q)`.
The associator description follows since all components are identities.
No pseudofunctor is built.
