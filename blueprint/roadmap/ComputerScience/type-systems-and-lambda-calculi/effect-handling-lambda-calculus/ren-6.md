# Renaming preserves the typing of computations

Let `ρ` be a renaming of de Bruijn
indices such that whenever `Γ` assigns the type `T` to the variable `i`, the context `Γ'`
assigns `T` to `ρ i`. If `Γ ⊢ c : C`, then `Γ' ⊢ c.ren ρ : C`.
