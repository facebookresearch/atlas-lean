# Tensoring commutes with module sheafification

Let `(C,J,R)` be a commutative ringed site at common universe `u`, with weak additive
sheafification, the locally-bijective comparison, monoidal `J.W`, and the underlying-ring
sheaf comparison. Put `L=PresheafOfModules.sheafificationCommId R`. For a module presheaf `A`,
there is a natural isomorphism `tensorLeft A ⋙ L ≅ L ⋙ tensorLeft L(A)`, whose component at
`B` identifies `L(A ⊗ B)` with `L(A) ⊗ L(B)` by the inverse monoidal tensor comparison.
