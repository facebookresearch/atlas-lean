# Semilinear Hom as a source functor

Let `R : Type r` be a semiring, `S : Type s` a commutative semiring, `σ : R →+* S`, and `N :
SemimoduleCat.{vN} S`. The functor `(SemimoduleCat.{vM} R)ᵒᵖ → SemimoduleCat.{max vM vN} S`
sends `M` to `M →ₛₗ[σ] N`; a linear map `a : M' → M` induces `f ↦ f ∘ a`.
