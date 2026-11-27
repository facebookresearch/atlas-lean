# Parallel substitution preserves the typing of operation clauses

Let `σ` be a
substitution such that whenever `Γ` assigns the type `T` to the variable `i`, the value `σ i`
has type `T` in `Γ'`. If the clauses `cls` have type `B ! Δ'` in `Γ`, then
`Clauses.subst σ cls` have type `B ! Δ'` in `Γ'`.
