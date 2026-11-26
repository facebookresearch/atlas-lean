# Applying an additive functor to the projective CE resolution computes its derived objects

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and T₀ = envelopingTrivialObject R L the lifted scalar U-module acted on through augmentation.
Assume Module.Projective R L. For an abelian D, additive F : ModuleCat.{max u v} U ⥤ D and n :
ℕ, H_n(F(envelopingComplex R L)) ≅ (F.leftDerived n).obj T₀.
