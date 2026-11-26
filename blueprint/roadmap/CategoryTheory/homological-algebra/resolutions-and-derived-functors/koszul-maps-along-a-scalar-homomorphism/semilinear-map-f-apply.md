# Each scalar-restricted chain-map component is the semilinear exterior map

Let k be a commutative ring, R and S commutative k-algebras, M an R-module and N an S-module.
Let φ : R →ₐ[k] S and f : M →ₛₗ[φ.toRingHom] N. Let x : M →ₗ[R] R and y : N →ₗ[S] S satisfy
y(f(m)) = φ(x(m)) for every m : M. For every n : ℕ and z : ⋀[R]^n M, the value of
(semilinearMap k φ x y f hf).f n on z equals exteriorPower.mapSemilinear φ.toRingHom f n z.
