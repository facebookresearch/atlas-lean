# An exact functor may be pulled out of a right derived functor wherever it is exact on the resolution used

**An exact functor may be pulled out of a right derived functor wherever it is exact on
the resolution used.**  For `P : D ⥤ A` and additive `F : A ⥤ B`, `E : B ⥤ B'`, if `E`
preserves the left homology of the degree-`n` short complex of `F` applied to the chosen
injective resolution of `P.obj X` for every `X : D`, then
`P ⋙ F.rightDerived n ⋙ E ≅ P ⋙ (F ⋙ E).rightDerived n`.

This is the form of `rightDerivedCompIso` available when `E` is exact only on the objects
reached by `P`; the degree-`n` right derived functor of `F` at `P.obj X` is the degree-`n`
homology of `F` applied to that resolution, so preserving its left homology is all that the
comparison uses.
