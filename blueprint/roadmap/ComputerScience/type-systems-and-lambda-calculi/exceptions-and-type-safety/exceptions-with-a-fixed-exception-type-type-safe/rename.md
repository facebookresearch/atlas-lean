# Renaming preserves typing

Let `exn` be the exception type, `Γ` and `Δ` contexts, and
`ρ` a renaming of de Bruijn indices such that whenever `Γ` assigns the type `B` to the variable
`x`, the context `Δ` assigns `B` to `ρ x`. If `e` has type `A` in `Γ`, then `e.rename ρ` has
type `A` in `Δ`.
