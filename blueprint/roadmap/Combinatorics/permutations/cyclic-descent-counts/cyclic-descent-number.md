# The cyclic descent count

Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. The count is `c(σ)=∑ i : Fin N, if σ(ρ i)<σ i then 1 else 0`;
the closing comparison is included.
