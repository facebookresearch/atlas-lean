# The positive-quotient coboundary precomposes with the quotient boundary

Let R be a commutative ring and equip ModuleCat.{v} R with a monoidal structure additive in
both variables. Let P : K₁ ⊗ K₂ ⟶ K₃ be a pairing of ℕ-indexed chain complexes. Assume K₁.d 1
0 = K₂.d 1 0 = 0, and let Q_P be the chain quotient of K₃ by S_n = positiveImages P n in each
degree, with projection π_P : K₃ ⟶ Q_P. For G : ModuleCat.{v} R, n : ℕ, φ : (Q_P)_n ⟶ G and x
: (Q_P)_(n+1), the coboundary satisfies (δφ)(x) = φ(d_Q(n+1,n)(x)). This is the degree-n to n
+ 1 differential of the linear Hom-cochain complex.
