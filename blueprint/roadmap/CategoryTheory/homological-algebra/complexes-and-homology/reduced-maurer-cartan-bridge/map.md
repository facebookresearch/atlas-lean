# Map

Reducedness is preserved by the bundled Maurer–Cartan map under explicit
augmentation compatibility: `η' ≫ ψ = η` on the coalgebra side and
`φ ≫ ε' = ε` on the algebra side. The proof reassociates the degree-zero
`ofHom` factors with the pinned cochain associativity lemmas, folds them with
`ofHom_comp`, rewrites with the two compatibility equalities, then closes with
the two vanishing hypotheses via `comp_zero` / `zero_comp`.
