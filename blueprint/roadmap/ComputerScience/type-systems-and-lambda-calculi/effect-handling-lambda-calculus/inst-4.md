# Single instantiation for values

If `w` has type `B` in `Γ` extended by an innermost
variable `x : A`, and `Γ ⊢ v : A`, then `Γ ⊢ w[v/x] : B`.
