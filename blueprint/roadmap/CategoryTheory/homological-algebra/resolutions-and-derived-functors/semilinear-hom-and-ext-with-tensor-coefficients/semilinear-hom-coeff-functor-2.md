# Module semilinear Hom as a coefficient functor

Let `R : Type r` be a ring, `S : Type s` a commutative ring, `σ : R →+* S`, and `M :
ModuleCat.{vM} R`. The functor `ModuleCat.{vN} S → ModuleCat.{max vM vN} S` sends `N` to `M
→ₛₗ[σ] N`, with pointwise scalar action. An `S`-linear map `b : N → N'` induces
postcomposition `f ↦ b ∘ f`.
