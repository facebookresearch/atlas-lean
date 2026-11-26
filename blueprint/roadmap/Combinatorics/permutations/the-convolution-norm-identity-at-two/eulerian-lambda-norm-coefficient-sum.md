# The convolution norm rotation-coefficient expansion

Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `a : ℚ`. Write
`P_(r,d)(X)=(1/r!)∏_(j=0)^(r-1)(X+j-d)`, `Λ_r(a)=∑ σ ∈ S_r, P_(r,descentNumber σ)(a) sign(σ)
[σ]`, and `N_n=∑ r : Fin N, sign(ρ^r.val) [ρ^r.val]` in the rational group rings. The
group-ring product is `Λ_N(a)N_n = ∑ σ ∈ S_N, (∑ r : Fin N, P_(N,d(σ*(ρ^r.val)⁻¹))(a)) sign(σ)
[σ]`.
