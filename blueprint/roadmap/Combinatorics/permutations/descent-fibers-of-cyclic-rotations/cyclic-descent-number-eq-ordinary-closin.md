# The cyclic count adds the closing comparison

Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. `c(σ)=descentNumber σ + (if σ 0<σ(Fin.last n) then 1 else 0)`.
