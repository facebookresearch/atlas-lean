# The degree map is the exterior Lie map tensored with the coefficient map

Let R be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism, M a left L-module and N a left
L'-module. Let g : M →ₗ⁅R,L⁆ f* N satisfy g(⁅x,m⁆) = ⁅f(x),g(m)⁆. For n : ℕ,
coefficientLieDegreeMap is ⋀[R]^n L ⊗[R] M →ₗ[R] ⋀[R]^n L' ⊗[R] N given by TensorProduct.map
(exteriorPower.map n f.toLinearMap) g.toLinearMap. Its value on a ⊗ m is ⋀^n f(a) ⊗ g(m).
