# Antipode Comp

Precomposition of an algebra homomorphism `f : H →ₐ[R] A` with the antipode `S` of
`H`, as an `R`-algebra homomorphism `H →ₐ[R] A`. Its underlying linear map is
`f.toLinearMap ∘ₗ HopfAlgebra.antipode R`. This is well-defined even when `H` is
noncommutative: `S` is an antihomomorphism (`HopfAlgebra.antipode_mul_antidistrib`), and `A` is
commutative, so `f ∘ S` is a homomorphism. The construction composes
`HopfAlgebra.antipodeAlgHomOp` with `AlgHom.fromOpposite`.
