# The top coefficient is sign divided by factorial

For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. For `σ ∈ S_n`,
`eulerianCoefficient n n σ = (n!:ℚ)⁻¹ * sign(σ)`.
