# Left whiskering is left tensoring

Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. For
an object `L` and morphism `f : M → N`, `(L ◁ f).hom=f.hom.lTensor L`, namely `id_L ⊗ f`.
