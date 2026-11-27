# Compatibility isomorphism for changing source and target

Let P, Q, A and B be categories, with functors i : P → A, j : Q → A, k : Q → B, F : P → Q and H
: A → B. Natural isomorphisms e_F : jF ≅ i and e_H : Hj ≅ k give sourceTargetCompatibility : Hi
≅ kF. Its forward map applies H to e_F⁻¹ and then uses e_H at F(Y).
