# The transported grade map is the tensor of the diagonal exterior maps

Let R be a commutative ring, M and N R-modules, m : ℕ, and e : X ≃ₗ[R] ⋀[R]^m (M × N) a linear
equivalence from an R-module X. Let M', N' and X' be R-modules with coordinates e' : X' ≃ₗ[R]
⋀[R]^m (M' × N'). Let f : M × N →ₗ[R] M' × N' and f.first : M →ₗ[R] M' satisfy f ∘ inl = inl'
∘ f.first, and put f.relative = snd' ∘ f ∘ inr. For q ≤ m, the induced quotient map G_q of
e'⁻¹ ∘ ⋀^m f ∘ e satisfies E'_q(G_q(z)) = TensorProduct.map (⋀^q f.first) (⋀^(m−q) f.relative)
(E_q(z)) for every source grade class z. Here E_q and E'_q are the mixed-tensor coordinate
equivalences of the transported adjacent-stage quotients.
