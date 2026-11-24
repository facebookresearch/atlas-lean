# Stable Steinberg Finite Torus Boundary Word

Every finite-torus element is a left cocycle defect times a boundary word.

Hypotheses: only `[Field F]` and `ht : t ∈ finiteTorusSubgroup n`. The proof is
structural `Subgroup.closure_induction`: `1` maps to `[]`, products concatenate
words, inverses reverse/invert words, and generators use the accepted
finite-pair reduction with the inverse letter rewritten by the same-index
cocycle identity. Orientation is head-left; defects commute left by centrality.

Nonclaims: the word is not canonical or minimal, no product-one condition on
coefficients is claimed, and no kernel consequence is drawn.
