# The right unitor uses the down scalar

Let `R : Type u` be a commutative ring, `v` a universe, and `h=max(u,v)`. Equip `ModuleCat.{h}
R` with the scoped tensor structure having tensor product over `R` and unit `ULift.{v} R`. For
`M : ModuleCat.{h} R`, `m : M`, and `r : ULift.{v} R`, the right unitor sends `m⊗r` to `r.down
• m`.
