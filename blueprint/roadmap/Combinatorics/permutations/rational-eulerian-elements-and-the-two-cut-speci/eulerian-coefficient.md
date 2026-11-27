# A signed Eulerian polynomial coefficient

For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. For `i : ℕ` and `σ ∈ S_n`,
`eulerianCoefficient n i σ = coeff_i(P_(n,d(σ))) * sign(σ)` in `ℚ`, with the sign coerced from
`ℤˣ` through `ℤ`.
