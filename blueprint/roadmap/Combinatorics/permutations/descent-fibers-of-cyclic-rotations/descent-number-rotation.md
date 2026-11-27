# The closing edge determines ordinary rotated descents

Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. For `r : Fin N`, `descentNumber(σ*ρ^r.val) = if closingDescent
σ r then c(σ)-1 else c(σ)`, with subtraction in `ℕ`.
