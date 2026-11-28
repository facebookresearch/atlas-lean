# Open₂ subst

Linear substitution of two terms into the body of a tensor elimination. When every finite set of
names misses some name (`[HasFresh Var]`): if `Δ, x : A, y : B ⊢ u.open₂ (fvar x) (fvar y) ∶ C` for
all distinct names `x` and `y` outside a finite set, `Γ₁ ⊢ s₁ ∶ A`, `Γ₂ ⊢ s₂ ∶ B`, and `Γ₁`, `Γ₂`
and `Δ` are pairwise disjoint, then `Γ₁, Γ₂, Δ ⊢ u.open₂ s₁ s₂ ∶ C`.
