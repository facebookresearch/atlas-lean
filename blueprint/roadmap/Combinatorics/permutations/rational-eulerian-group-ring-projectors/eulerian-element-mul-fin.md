# Supported Eulerian elements are orthogonal idempotents

For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)`, `P_(n,d)(X) = (1/n!)∏_(j=0)^(n-1)(X+j-d)`, and
`Λ_n(t) = ∑ σ ∈ S_n, P_(n,descentNumber σ)(t) sign(σ) [σ]` in `ℚ[S_n]`. Write `ε_(n,i)` for
the coefficient of `t^i` in this family. For `i,j : Fin(n+1)`, `ε_(n,i.val) * ε_(n,j.val) = if
i=j then ε_(n,i.val) else 0`.
