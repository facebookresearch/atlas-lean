# The enveloping algebra is a coefficient Lie-module object

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. regularCoefficients R L is U in LieModuleCat.{max u v} R L with Lie action ⁅x,a⁆
= −a*ι(x) and its R-algebra module structure.
