# Module semilinear Hom as a bifunctor

Let `R : Type r` be a ring, `S : Type s` a commutative ring, and `σ : R →+* S`. The bifunctor
`(ModuleCat.{vM} R)ᵒᵖ ⥤ ModuleCat.{vN} S ⥤ ModuleCat.{max vM vN} S` has value `M →ₛₗ[σ] N`.
For `a : M' → M` and `b : N → N'`, the induced map is `f ↦ b ∘ f ∘ a`; the source and
coefficient carrier universes are independent.
