# The left coefficient module lifts to the common enveloping category

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. liftedLeftCoefficient is the image of M under ModuleCat.uliftFunctor from
its carrier universe w to H, using the additional lift max u v. It carries the transported
left U-action.
