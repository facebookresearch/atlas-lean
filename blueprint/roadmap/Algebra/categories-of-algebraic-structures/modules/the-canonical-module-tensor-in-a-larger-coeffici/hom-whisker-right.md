# Right whiskering is right tensoring

Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. For
a morphism `f : L → M` and object `N`, `(f ▷ N).hom=f.hom.rTensor N`, namely `f ⊗ id_N`.
