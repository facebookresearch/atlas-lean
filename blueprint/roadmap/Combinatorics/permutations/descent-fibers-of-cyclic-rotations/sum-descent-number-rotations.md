# The weighted descent sum over all rotations

Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `σ ∈ S_N = Equiv.Perm (Fin N)`. Write
`c(σ)=cyclicDescentNumber σ`, counting positions `i : Fin N` with `σ(ρ i)<σ i`. Products
compose as `(u*v)(i)=u(v(i))`. For a commutative additive monoid `T` and `f : ℕ → T`, `∑ r :
Fin N, f(descentNumber(σ*ρ^r.val)) = c(σ) • f(c(σ)-1) + (N-c(σ)) • f(c(σ))`. The scalar action
is repeated addition, and the two weights count the closing-descent and non-descent parts.
