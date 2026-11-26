# Semilinear Hom as a coefficient functor

Let `R : Type r` be a semiring, `S : Type s` a commutative semiring, `σ : R →+* S`, and `M :
SemimoduleCat.{vM} R`. The functor `SemimoduleCat.{vN} S → SemimoduleCat.{max vM vN} S` sends
`N` to `M →ₛₗ[σ] N`, with pointwise `S`-action. Its map on `f : N → N'` is postcomposition `a
↦ f ∘ a`.
