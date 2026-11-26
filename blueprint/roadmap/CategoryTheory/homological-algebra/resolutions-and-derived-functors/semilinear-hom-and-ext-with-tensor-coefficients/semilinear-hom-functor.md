# Semilinear Hom as a contravariant-covariant bifunctor

Let `R : Type r` be a semiring, `S : Type s` a commutative semiring, and `σ : R →+* S`. The
bifunctor `(SemimoduleCat.{vM} R)ᵒᵖ ⥤ SemimoduleCat.{vN} S ⥤ SemimoduleCat.{max vM vN} S` has
value `M →ₛₗ[σ] N`. A source map `a : M' → M` acts by precomposition, and a coefficient map `b
: N → N'` acts by postcomposition.
