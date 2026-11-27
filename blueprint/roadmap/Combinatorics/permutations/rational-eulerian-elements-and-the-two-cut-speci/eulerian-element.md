# The Eulerian coefficient element

For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)` and `d(σ) = descentNumber σ`. Put `P_(n,d)(X) =
(1/n!) ∏_(j=0)^(n-1)(X+j-d)` in `ℚ[X]`, with empty product `1`. For `i : ℕ`, `eulerianElement
n i` is `∑ σ ∈ S_n, coeff_i(P_(n,d(σ))) * sign(σ) [σ]` in `ℚ[S_n]`.
