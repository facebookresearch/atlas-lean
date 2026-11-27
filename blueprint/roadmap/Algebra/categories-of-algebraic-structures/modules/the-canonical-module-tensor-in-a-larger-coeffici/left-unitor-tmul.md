# The left unitor uses the down scalar

Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. For
`M : ModuleCat.{h} R`, `r : ULift.{v} R`, and `m : M`, the left unitor sends `r⊗m` to `r.down
• m`.
