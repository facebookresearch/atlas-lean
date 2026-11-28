# Open subst

Linear substitution into a body opened by one fresh name, as in a β-step. When every finite set
of names misses some name (`[HasFresh Var]`): if `Δ, x : A ⊢ t ^ fvar x ∶ B` for every name `x`
outside a finite set, `Γ ⊢ s ∶ A`, and `Γ` and `Δ` are disjoint, then `Γ, Δ ⊢ t ^ s ∶ B`.
