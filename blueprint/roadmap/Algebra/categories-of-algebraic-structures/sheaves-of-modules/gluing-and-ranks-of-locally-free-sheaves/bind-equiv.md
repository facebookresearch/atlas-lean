# Equivalence between direct and iterated slice module categories

Let `C' : Type u₂` have morphism universe `v₂`, `J'` be a topology, and `S : Sheaf J'
RingCat.{u}`. For `X∈C'` and `Y∈Over X`, `LocalGeneratorsData.bindEquiv Y` is the canonical
equivalence `SheafOfModules(S.over Y.left) ≌ SheafOfModules((S.over X).over Y)`.
