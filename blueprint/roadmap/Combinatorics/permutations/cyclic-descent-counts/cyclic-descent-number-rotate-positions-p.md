# Position rotation preserves cyclic descents

Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. For every `r : ℕ`, right multiplication rotates positions and
satisfies `c(σ*ρ^r)=c(σ)`.
