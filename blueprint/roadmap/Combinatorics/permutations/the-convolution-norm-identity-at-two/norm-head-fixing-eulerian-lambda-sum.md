# The head-fixed norm expansion

Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `a : ℚ`. Write
`P_(r,d)(X)=(1/r!)∏_(j=0)^(r-1)(X+j-d)`, `Λ_r(a)=∑ σ ∈ S_r, P_(r,descentNumber σ)(a) sign(σ)
[σ]`, and `N_n=∑ r : Fin N, sign(ρ^r.val) [ρ^r.val]` in the rational group rings. If `H_n` is
the fixed-head group-ring map, `N_n H_n(Λ_n(a)) = ∑ r : Fin N, ∑ π ∈ S_n, P_(n,d(π))(a)
sign(ρ^r.val * H_n(π)) [ρ^r.val * H_n(π)]`, with `H_n(π)` denoting its permutation embedding
in the summand.
