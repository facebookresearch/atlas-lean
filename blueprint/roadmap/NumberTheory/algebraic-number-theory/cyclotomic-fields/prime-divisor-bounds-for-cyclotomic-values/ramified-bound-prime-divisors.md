# Ramified bound on the number of prime divisors of $x^n - 1$

The ramified bound. Let `n = ∏_{i=1}^m p_i^{a_i}` with primes `p_1 < ⋯ < p_m` (the ordering
the source fixes at the start of its Section 5), `x > 1`, `ω_n = ω(x^n - 1)`, and, with
`p_0 := 1`, let `r_{i,j}` be the `i`-th element (`Nat.nth`, `0`-indexed here) of
`Π^j = {ρ prime : ρ ≡ 1 (mod p_j), ρ ≢ 1 (mod p_s) for j < s ≤ m}`. Fix a prime factor `p_α` of
`n` and write `p_α = r_{b,τ}` with `τ ≤ m`. As in `hybrid_bound_prime_divisors`, the source's
`x ≥ min_{k_0 + ⋯ + k_m = ω_n} max_t (1 + ∏_{j ≤ t} δ_α(j) ∏_{i ≤ k_j} r_{i,j})^{T(t)}` is stated
as the existence of a composition `k` (parts in `ℕ`, not `ℤ⁺`) meeting every bound after raising
to the power `∏_{s ≤ t} p_s^{a_s}`. The factors `δ_α(j)` are applied to the block products: if
`p_α ∣ x^n - 1`, block `τ` with `k_τ < b` (`1`-indexed in the source, `k_τ ≤ b` here) has its
largest factor `r_{k_τ,τ}` replaced by `p_α`, and block `α` gains the factor `p_α^{a_α}`; if
`p_α ∤ x^n - 1`, block `τ` with `k_τ ≥ b` drops `p_α` and takes the next element instead. In
the divisible case the composition also has `k_τ > 0` (the source's `δ_α(τ)` is undefined at
`k_τ = 0`). The source's worked example (`n = 3`, `ω_3 = 10`: `x ≥ 4387` if `3 ∣ x^3 - 1`,
`x ≥ 5423` otherwise) is reproduced exactly by this reading. Definitions follow the arXiv version
(arXiv:2412.00010), whose statement matches the journal record.

## Sources

- Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95, Theorem 2.
