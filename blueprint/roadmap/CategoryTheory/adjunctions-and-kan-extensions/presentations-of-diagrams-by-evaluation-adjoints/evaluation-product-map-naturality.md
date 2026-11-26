# Evaluation-adjoint product assembly is natural

Suppose the evaluation right adjoints exist for categories `I`, `C`. Given
diagrams `F`, `G`, maps `e(k) : F(k) → A(k)`, `e′(k) : G(k) → B(k)`, a diagram
morphism `φ : F → G` and maps `a(k) : A(k) → B(k)`, assume
`φ(k) ≫ e′(k) = e(k) ≫ a(k)` for every `k`. If both right-adjoint products exist,
then `φ ≫ assemble(e′) = assemble(e) ≫ ∏_k R_k(a(k))`.
