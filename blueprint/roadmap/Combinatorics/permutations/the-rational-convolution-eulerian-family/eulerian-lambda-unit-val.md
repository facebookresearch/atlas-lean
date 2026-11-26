# The convolution unit has the parameter value

For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. Write `ε_(n,i) = ∑ σ ∈ S_n,
coeff_i(P_(n,d(σ))) * sign(σ) [σ]` and `Λ_n(t) = ∑ σ ∈ S_n, P_(n,d(σ))(t) * sign(σ) [σ]` in
`ℚ[S_n]`. For `a : ℚ` with `a≠0`, `(eulerianLambdaUnit n a ha).val = Λ_n(a)`.
