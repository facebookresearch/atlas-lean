# The semilinear Koszul map sends a wedge to the wedge of generator images

Let k be a commutative ring, R and S commutative k-algebras, M an R-module and N an S-module.
Let φ : R →ₐ[k] S and f : M →ₛₗ[φ.toRingHom] N. Let x : M →ₗ[R] R and y : N →ₗ[S] S satisfy
y(f(m)) = φ(x(m)) for every m : M. For n : ℕ and a : Fin n → M, the degree-n component of
semilinearMap sends exteriorPower.ιMulti R n a to exteriorPower.ιMulti S n (fun j => f(a_j)).
