# A mixed tensor class maps through the two diagonal exterior maps

Let R be a commutative ring and M, N, M', N' R-modules. Let f.map : M × N →ₗ[R] M' × N' and
f.first : M →ₗ[R] M' satisfy f.map ∘ inl = inl' ∘ f.first. Put f.relative = snd' ∘ f.map ∘
inr. For q ≤ m, x : ⋀[R]^q M and y : ⋀[R]^(m−q) N, f.gradeMap sends mixedClass(x ⊗ y) to
mixedClass'(⋀^q f.first(x) ⊗ ⋀^(m−q) f.relative(y)). Terms from the N-to-M' component of f lie
in stage q + 1 and are zero in this quotient.
