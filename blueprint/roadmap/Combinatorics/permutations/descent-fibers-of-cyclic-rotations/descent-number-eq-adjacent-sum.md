# Ordinary descents are the adjacent comparison sum

Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. The ordinary count is `descentNumber σ = ∑ i : Fin n, if
σ(i.succ)<σ(i.castSucc) then 1 else 0`, omitting the closing edge.
