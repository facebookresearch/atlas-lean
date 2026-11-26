# Lifted resolution Hom-cochains agree with Hom from the unlifted CE complex

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. Assume Module.Free R L. The degreewise up/down Hom equivalences give
liftedEnvelopingHomComplex R L M ≅ envelopingHomComplex R L M, with degree-n coordinate f ↦ (z
↦ down(f(up(z)))). The target cochains are U-linear maps C_n → M with boundary precomposition.
