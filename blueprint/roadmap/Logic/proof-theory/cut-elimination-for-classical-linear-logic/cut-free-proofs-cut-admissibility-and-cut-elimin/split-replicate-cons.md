# Case split of a cons against replicated copies

Given `Multiset.replicate n a + Γ = b ::ₘ Δ`, either the head `b` is one of the
`n` copies of `a` (so `b = a` and the tail is `replicate (n-1) a + Γ`), or `b` belongs to
`Γ` (so `Δ = Multiset.replicate n a + Γ'` where `Γ = b ::ₘ Γ'`).
The tail `Δ` can be an arbitrary multiset; the residual list is obtained from `Γ`.
