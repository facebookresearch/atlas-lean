# Matrix of cross products of the columns

For a real `3 × 3` matrix `B` with columns `a₁`, `a₂`, `a₃`, the cross-column matrix is the real
`3 × 3` matrix whose `j`-th column is `a_{j+1} × a_{j+2}`, indices modulo `3`: its columns are
`a₂ × a₃`, `a₃ × a₁` and `a₁ × a₂`. It is defined for every `B`, singular or not, and equals the
transpose of the adjugate of `B` ([identity](cross-columns-eq-transpose-adjugate.md)).
