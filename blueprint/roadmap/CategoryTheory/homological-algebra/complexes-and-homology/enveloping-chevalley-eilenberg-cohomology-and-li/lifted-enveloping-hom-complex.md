# Linear Yoneda cochains of the lifted enveloping projective resolution

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. Assume Module.Free R L. liftedEnvelopingHomComplex is the ℕ-indexed
R-module cochain complex obtained by applying the linear Yoneda functor
Hom_U(−,liftedLeftCoefficient M) to the lifted projective resolution.
