# Tensor morphisms act factor by factor

Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. For
`f : K → L`, `g : M → N`, `x : K`, and `y : M`, `(f ⊗ₘ g)(x⊗y)=f(x)⊗g(y)`.
