# Renaming preserves the typing of operation clauses

Let `ρ` be a renaming of de Bruijn
indices such that whenever `Γ` assigns the type `T` to the variable `i`, the context `Γ'`
assigns `T` to `ρ i`. If the clauses `cls` have type `B ! Δ'` in `Γ`, then the renamed clauses
`Clauses.ren ρ cls` have type `B ! Δ'` in `Γ'`.
