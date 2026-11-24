# Cross Columns

The matrix whose `j`-th column is the cross product `B.col (j + 1) ⨯₃ B.col (j + 2)`, indices
modulo `3`: for the columns `a₁ a₂ a₃` of `B`, its columns are `a₂ ⨯₃ a₃`, `a₃ ⨯₃ a₁` and
`a₁ ⨯₃ a₂`. It is the transpose of the adjugate of `B` (`crossColumns_eq_transpose_adjugate`).
