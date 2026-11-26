# Compatible semilinear data give a scalar-restricted Koszul chain map

Let k be a commutative ring, R and S commutative k-algebras, M an R-module and N an S-module.
Let φ : R →ₐ[k] S and f : M →ₛₗ[φ.toRingHom] N. Let x : M →ₗ[R] R and y : N →ₗ[S] S satisfy
y(f(m)) = φ(x(m)) for every m : M. The degree maps exteriorPower.mapSemilinear φ.toRingHom f n
form a chain map from the Koszul complex on (R, M, x), restricted to k, to the Koszul complex
on (S, N, y), restricted to k. Both complexes retain their down-ℕ shape.
