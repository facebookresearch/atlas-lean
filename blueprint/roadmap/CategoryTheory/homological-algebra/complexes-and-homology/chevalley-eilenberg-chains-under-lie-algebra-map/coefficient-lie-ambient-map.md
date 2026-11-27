# Joint Lie and coefficient maps induce an ambient exterior tensor map

Let R be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism, M a left L-module and N a left
L'-module. Let g : M →ₗ⁅R,L⁆ f* N satisfy g(⁅x,m⁆) = ⁅f(x),g(m)⁆. Define
coefficientLieAmbientMap : ExteriorAlgebra R L ⊗[R] M →ₗ[R] ExteriorAlgebra R L' ⊗[R] N as
ExteriorAlgebra.map f tensored with g. It sends a ⊗ m to ExteriorAlgebra.map f(a) ⊗ g(m).
