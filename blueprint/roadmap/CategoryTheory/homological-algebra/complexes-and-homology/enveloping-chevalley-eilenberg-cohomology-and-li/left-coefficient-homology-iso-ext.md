# Left exterior coefficient cohomology computes enveloping Ext

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. Assume Module.Free R L. For n : ℕ, leftCoefficientHomologyIsoExt
identifies H^n(leftCoefficientCochainComplex R L M) with leftEnvelopingExt R L M n. The source
has terms Hom_R(⋀[R]^n L,M); the comparison uses its enveloping Hom coordinates, the lift Hom
isomorphism and the projective-resolution Ext comparison.
