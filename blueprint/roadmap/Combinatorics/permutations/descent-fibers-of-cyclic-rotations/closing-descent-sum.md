# The closing-edge count is the cyclic descent count

Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. `∑ r : Fin N, if closingDescent σ r then 1 else 0 = c(σ)`.
Every cyclic edge occurs once as the closing edge of a rotation.
