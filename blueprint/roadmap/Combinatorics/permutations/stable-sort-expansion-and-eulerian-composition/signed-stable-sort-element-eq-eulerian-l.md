# The sorting sum is Eulerian evaluation

For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)`, `P_(n,d)(X) = (1/n!)∏_(j=0)^(n-1)(X+j-d)`, and
`Λ_n(t) = ∑ σ ∈ S_n, P_(n,descentNumber σ)(t) sign(σ) [σ]` in `ℚ[S_n]`. For every `m : ℕ`,
`signedStableSortElement n m = Λ_n(m)`.
