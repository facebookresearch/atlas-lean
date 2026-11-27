# Parallel substitution preserves the typing of computations

Let `σ` be a substitution
such that whenever `Γ` assigns the type `T` to the variable `i`, the value `σ i` has type `T` in
`Γ'`. If `Γ ⊢ c : C`, then `Γ' ⊢ c.subst σ : C`.
