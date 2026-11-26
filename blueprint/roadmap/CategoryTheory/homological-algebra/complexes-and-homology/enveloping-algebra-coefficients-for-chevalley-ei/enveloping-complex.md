# Commuting left multiplication makes the regular CE complex U-linear

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U =
UniversalEnvelopingAlgebra R L, ι : L →ₗ⁅R⁆ U its generator map and ε : U →ₐ[R] R its
augmentation. Give U the left Lie action ⁅x,a⁆ = −a*ι(x), and let C_n = ⋀[R]^n L ⊗[R] U be its
CE coefficient terms. envelopingComplex R L is the chain complex in ModuleCat.{max u v} U
obtained from the coefficient complex by its commuting left U-action. The underlying terms C_n
and boundary functions are those of regularCoefficientComplex.
