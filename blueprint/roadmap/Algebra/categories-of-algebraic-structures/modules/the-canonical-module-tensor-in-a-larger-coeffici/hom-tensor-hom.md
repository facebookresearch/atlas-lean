# Tensor morphisms are tensor maps of linear maps

Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. For
`f : K → L` and `g : M → N` in this category, `(f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom`.
