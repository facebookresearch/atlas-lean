# Module semilinear Hom as a source functor

Let `R : Type r` be a ring, `S : Type s` a commutative ring, `σ : R →+* S`, and `N :
ModuleCat.{vN} S`. The functor `(ModuleCat.{vM} R)ᵒᵖ → ModuleCat.{max vM vN} S` sends an
arbitrary `R`-module `M` to `M →ₛₗ[σ] N`. Its map on `a : M' → M` is precomposition `f ↦ f ∘
a`.
