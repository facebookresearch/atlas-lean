# Lift

For an abelian group `A` and a function `φ : Skeleton C → A`, assume
`φ (toSkeleton S.X₂) = φ (toSkeleton S.X₁) + φ (toSkeleton S.X₃)` for
every short complex `S` admissible exact in the chosen structure on `C`.
The induced additive homomorphism `K0 C →+ A` sends every `K0.mk X` to
`φ (toSkeleton X)`. It is unique among additive homomorphisms with these
values on every object class, as expressed by `K0.lift_unique`.
