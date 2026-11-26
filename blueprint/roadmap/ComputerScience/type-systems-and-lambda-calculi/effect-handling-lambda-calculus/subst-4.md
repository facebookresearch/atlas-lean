# Parallel substitution preserves the typing of values

Let `σ` be a substitution such
that whenever `Γ` assigns the type `T` to the variable `i`, the value `σ i` has type `T` in
`Γ'`. If `Γ ⊢ v : A`, then `Γ' ⊢ v.subst σ : A`.
