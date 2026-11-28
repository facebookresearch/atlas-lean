# Renaming preserves the typing of contexts

Let `T` be the answer type, `Γ` and `Δ`
contexts, and `ρ` a renaming of de Bruijn indices such that whenever `Γ` assigns the type `C` to
the variable `x`, the context `Δ` assigns `C` to `ρ x`. If `E` has type `A` to `B` in `Γ`, then
`E.rename ρ` has type `A` to `B` in `Δ`.
