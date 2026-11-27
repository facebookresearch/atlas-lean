# The lifted scalar module carries the trivial enveloping action

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. envelopingTrivialObject R L is ULift.{max u v} R in ModuleCat.{max u v} U, with
a • ULift.up r = ULift.up (ε(a)*r).
