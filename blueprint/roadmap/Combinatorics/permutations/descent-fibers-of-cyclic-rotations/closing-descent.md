# The closing descent of a rotated word

Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. For `r : Fin N`, `closingDescent σ r` is the predicate
`(σ*ρ^r.val) 0 < (σ*ρ^r.val)(Fin.last n)`.
