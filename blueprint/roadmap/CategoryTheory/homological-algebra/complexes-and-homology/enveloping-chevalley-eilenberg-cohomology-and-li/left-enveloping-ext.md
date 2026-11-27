# The first-variable linear Ext term uses the lifted trivial and coefficient modules

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. For n : ℕ, leftEnvelopingExt R L M n is the R-linear Ext module in the
category ModuleCat.{H} U, evaluated contravariantly at E(T₀) and covariantly at
liftedLeftCoefficient M. It is Ext_U^n(E(T₀),liftedLeftCoefficient M).
