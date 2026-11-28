# Parallel substitution preserves typing

Let `exn` be the exception type, `Γ` and `Δ`
contexts, and `σ` a substitution such that whenever `Γ` assigns the type `B` to the variable
`x`, the term `σ x` has type `B` in `Δ`. If `e` has type `A` in `Γ`, then `e.subst σ` has type
`A` in `Δ`.
