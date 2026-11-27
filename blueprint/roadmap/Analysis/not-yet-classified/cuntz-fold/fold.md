# Fold

Let `S` be a monoid acting additively on a star semiring `R`, compatibly with multiplication on both
sides. Let `ι` be finite with decidable equality. For a family `v : ι → R` satisfying `star (v i) *
v j = δij` and `∑ i, v i * star (v i) = 1`, the matrix fold is a star-algebra equivalence
`CStarMatrix ι ι R ≃⋆ₐ[S] R`. It sends `X` to `∑ i,j, v i * X i j * star (v j)`; its inverse sends
`z` to the matrix with entry `star (v i) * z * v j`. Here `δij` is one when `i = j` and zero
otherwise.
