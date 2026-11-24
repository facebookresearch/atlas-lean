# Nat Iso Of Quasi Iso At

Degreewise homology natural isomorphism induced by a pointwise `QuasiIsoAt`.

For `K L : J ⥤ HomologicalComplex C c` and `f : K ⟶ L` such that each
`f.app j` is a `QuasiIsoAt` in degree `i`, postcomposition with
`homologyFunctor C c i` yields a natural isomorphism
`K ⋙ homologyFunctor C c i ≅ L ⋙ homologyFunctor C c i`.

The proof right-whiskers `f` with the homology functor, installs
`IsIso` at each object from `hf`, and promotes via `NatIso.isIso_of_isIso_app`.
