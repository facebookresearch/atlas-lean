# Typing of operation clauses

`HasClauses sig Γ cls B Δ'` holds when every clause
`o(x; k) ↦ c` of `cls` has type `B ! Δ'` in `Γ` extended by `x : A_o` (index `1`) and
`k : B_o → B ! Δ'` (index `0`). Shadowed clauses are typed too.
