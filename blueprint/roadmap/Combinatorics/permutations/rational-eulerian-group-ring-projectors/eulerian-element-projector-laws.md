# The complete Eulerian projector laws

For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)`, `P_(n,d)(X) = (1/n!)∏_(j=0)^(n-1)(X+j-d)`, and
`Λ_n(t) = ∑ σ ∈ S_n, P_(n,descentNumber σ)(t) sign(σ) [σ]` in `ℚ[S_n]`. Write `ε_(n,i)` for
the coefficient of `t^i` in this family. The identities are `∑ i : Fin(n+1), ε_(n,i.val)=1`
and, for all `i,j : ℕ`, `ε_(n,i)*ε_(n,j)=if i=j then ε_(n,i) else 0`. Weights above `n` are
thereby included with zero value.
