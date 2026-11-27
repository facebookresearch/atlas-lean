# The inverse-rotation sum at two

Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, `r₀ : Fin N`, and `π ∈ S_n`. Put `σ = ρ^r₀.val *
headFixingHom n π` and `P_(r,d)(X)=(1/r!)∏_(j=0)^(r-1)(X+j-d)` in `ℚ[X]`. The
inverse-position-rotation sum satisfies `∑ r : Fin N, P_(N,descentNumber(σ*(ρ^r.val)⁻¹))(2) =
2 * P_(n,descentNumber π)(2)`, including the empty tail.
