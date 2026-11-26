# Joint right chain maps compose in the given order

Let R be commutative, L,L' R-Lie algebras, M a right L-module, N a right L'-module, f : L
→ₗ⁅R⁆ L' and g : RightLieModuleCat.HomOver f M N. Thus g is R-linear and g(m·x) = g(m)·f(x).
For the bundled chain maps, the Lie carriers share universe v and coefficient carriers share
w. For h : L' →L'' and k : HomOver h N P in the same respective carrier universes,
rightCoefficientLieComplexMap(f,g) ≫ rightCoefficientLieComplexMap(h,k) equals the map for
h.comp f and HomOver.comp k g.
