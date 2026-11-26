# Degreewise exterior coordinates give an isomorphism to the transported complex

Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let K : ChainComplex (ModuleCat.{max u v} R) ℕ and e_n : K.X n ≅ chainObject R L n
for every n, where chainObject has carrier ⋀[R]^n L. Then K ≅ (ChainData.ofComplex R L K
e).complex, whose boundary is e_(n+1).inv ≫ K.d (n + 1) n ≫ e_n.hom. The forward and inverse
components are e_n.hom and e_n.inv.
