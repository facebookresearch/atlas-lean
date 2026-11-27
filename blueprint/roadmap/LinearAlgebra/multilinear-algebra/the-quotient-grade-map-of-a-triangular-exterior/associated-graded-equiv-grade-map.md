# The associated-grade coordinate map is the diagonal exterior tensor map

Let R be a commutative ring and M, N, M', N' R-modules. Let f.map : M × N →ₗ[R] M' × N' and
f.first : M →ₗ[R] M' satisfy f.map ∘ inl = inl' ∘ f.first. Put f.relative = snd' ∘ f.map ∘
inr. For q ≤ m and a source associated-grade class z, let E_q and E'_q be the complementary
mixed-tensor coordinate equivalences. Then E'_q(f.gradeMap m q z) = TensorProduct.map
(exteriorPower.map q f.first) (exteriorPower.map (m − q) f.relative) (E_q(z)).
