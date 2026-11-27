# Double instantiation

If `c` has type `C` in `Γ` extended by `x : A` (index `1`) and
`k : K` (index `0`), and `Γ ⊢ x' : A` and `Γ ⊢ k' : K`, then `Γ ⊢ c[x'/x, k'/k] : C`. With
`A = A_o`, `K = B_o → B ! Δ'` and `C = B ! Δ'` this types the instantiated operation clause of
the handler rule.
