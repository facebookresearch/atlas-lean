# Comparing iterated and composite source changes

Let P, Q and S be preadditive, A abelian, and i : P → A, j : Q → A, k : S → A additive. Given
additive F : P → Q and G : Q → S with e_F : jF ≅ i and e_G : kG ≅ j, and a finite resolution R
of X relative to i, mapSourceCompMap compares the resolving complex obtained by first F and then
G with that obtained by GF using sourceCompCompatibility. It is the canonical comparison G(F(R))
→ (GF)(R).
