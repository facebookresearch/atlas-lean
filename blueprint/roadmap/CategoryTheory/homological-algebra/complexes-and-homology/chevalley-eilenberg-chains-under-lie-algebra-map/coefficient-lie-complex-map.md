# Joint naturality defines a CE coefficient chain map

Let R be commutative, f : L →ₗ⁅R⁆ L' a Lie homomorphism, M a left L-module and N a left
L'-module. Let g : M →ₗ⁅R,L⁆ f* N satisfy g(⁅x,m⁆) = ⁅f(x),g(m)⁆. For the bundled complexes, L
and L' have the same carrier universe v and M and N the same carrier universe w, with chain
terms in ModuleCat.{max u v w} R. The maps F_n = ⋀^n f ⊗ g assemble into
coefficientLieComplexMap : coefficientComplex R L M ⟶ coefficientComplex R L' N. Its degree-n
component sends a ⊗ m to ⋀^n f(a) ⊗ g(m).
