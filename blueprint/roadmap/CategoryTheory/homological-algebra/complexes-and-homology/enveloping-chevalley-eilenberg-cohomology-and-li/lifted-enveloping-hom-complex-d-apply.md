# The lifted resolution Hom differential is precomposition with its boundary

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. Assume Module.Free R L. For n : ℕ and a lifted cochain f, the differential
from n to n + 1 is P_lift.complex.d (n + 1) n ≫ f. This is positive precomposition, with no
extra degree sign.
