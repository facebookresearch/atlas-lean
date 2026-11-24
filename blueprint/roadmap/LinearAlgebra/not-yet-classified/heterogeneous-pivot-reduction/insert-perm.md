# Insert Perm

Insertion of a pivot into a deleted permutation.

Given `c : n`, `r : m` and `e : DeletedIndex n c ≃ DeletedIndex m r`,
build `n ≃ m` sending `c ↦ r` and `j ≠ c ↦ (e ⟨j, _⟩).val`.
Orientation matches `deletePerm`: column → row via `σ`.

The `toFun`/`invFun` are defined inline via `where` so that `left_inv`/`right_inv`
goals already contain the `if`-branch; each branch is then closed with
`simp only [dite_eq_left/dite_eq_right]`.
