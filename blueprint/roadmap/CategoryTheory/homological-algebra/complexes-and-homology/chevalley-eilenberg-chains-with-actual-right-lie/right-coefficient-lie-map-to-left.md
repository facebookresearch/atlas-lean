# A right-equivariant coefficient map is equivariant after left conversion

Let R be commutative, L,L' R-Lie algebras, M a right L-module, N a right L'-module, f : L
→ₗ⁅R⁆ L' and g : RightLieModuleCat.HomOver f M N. Thus g is R-linear and g(m·x) = g(m)·f(x).
The same R-linear g defines rightCoefficientLieMapToLeft : M_left →ₗ⁅R,L⁆ f* N_left, where the
converted left actions are negatives of the right actions.
