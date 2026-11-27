# Up/down coordinates identify lifted module Hom with unlifted enveloping Hom

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Put h₀ = max u v and H
= max u v w. Let E : ModuleCat.{h₀} U ⥤ ModuleCat.{H} U be the ULift functor, T₀ the scalar
module ULift R acted on through augmentation, and M : ModuleCat.{w} U an arbitrary left
coefficient module. For n : ℕ, liftedEnvelopingHomCoordinates is an R-linear equivalence
Hom_U(E(C_n),liftedLeftCoefficient M) ≃ₗ[R] Hom_U(C_n,M). Its forward map sends f to z ↦
down(f(up(z))); its inverse sends a map a to the module morphism up(z) ↦ up(a(z)).
