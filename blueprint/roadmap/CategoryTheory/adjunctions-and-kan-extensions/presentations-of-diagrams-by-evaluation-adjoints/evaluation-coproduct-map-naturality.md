# Evaluation-adjoint coproduct assembly is natural

Suppose the evaluation left adjoints exist for categories `I`, `C`. Given
diagrams `F`, `G`, maps `e(k) : A(k) → F(k)`, `e′(k) : B(k) → G(k)`, a diagram
morphism `φ : F → G` and maps `a(k) : A(k) → B(k)`, assume
`a(k) ≫ e′(k) = e(k) ≫ φ(k)` for every `k`. If both left-adjoint coproducts exist,
then `∐_k L_k(a(k)) ≫ assemble(e′) = assemble(e) ≫ φ`.
