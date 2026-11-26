# Restricted additive sheafification units are local equivalences

Let `C : Type u` have morphism universe `u`, `J` be a topology, `X∈C`, and `P : Cᵒᵖ ⥤ Ab.{u}`.
Assume weak additive sheafification on `J` and the locally-bijective characterization of `W`
on both `J` and `J.over X`. Then precomposition of `toSheafify J P` by `(Over.forget X).op`
belongs to `(J.over X).W`. Thus the restricted sheafification unit is a local equivalence on
the slice.
