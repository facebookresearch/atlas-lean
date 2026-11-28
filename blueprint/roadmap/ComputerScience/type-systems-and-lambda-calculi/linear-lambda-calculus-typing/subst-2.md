# Linear substitution

**Linear substitution** (Property 1 of Pfenning's lecture notes on linear functional
programming, 15-814, Lecture 19): when every finite set of names misses some name
(`[HasFresh Var]`), if `Γ ⊢ s ∶ A` and `Δ, x : A ⊢ t ∶ B` with `Γ` and `Δ` disjoint, then
`Γ, Δ ⊢ t[x := s] ∶ B`.
