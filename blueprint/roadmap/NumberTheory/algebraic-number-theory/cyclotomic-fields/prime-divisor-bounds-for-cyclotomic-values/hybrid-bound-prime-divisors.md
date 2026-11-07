# Hybrid bound for prime divisors of $x^n - 1$

The hybrid bound. Let `n = ∏_{i=1}^m p_i^{a_i}` with distinct primes `p_i` (in any order),
`x > 1`, and `ω_n = ω(x^n - 1)`. With `p_0 := 1`, let
`Π^j = {ρ prime : ρ ≡ 1 (mod p_j), ρ ≢ 1 (mod p_s) for j < s ≤ m}` and `r_{i,j}` its `i`-th
element (`Nat.nth`, `0`-indexed here). The source's
`x ≥ min_{k_0 + ⋯ + k_m = ω_n} max_{0 ≤ t ≤ m} (1 + ∏_{j ≤ t} ∏_{i ≤ k_j} r_{i,j})^{T(t)}` with
`T(t) = ∏_{s=1}^t p_s^{-a_s}` is stated equivalently, after raising to the power
`∏_{s ≤ t} p_s^{a_s}`, as the existence of a composition `k` meeting every bound. The parts `k_j`
range over `ℕ` (the source writes `k_i ∈ ℤ⁺`; with positive parts the claim fails for
`n = 3`, `x = 2`, where `x^3 - 1 = 7` and `ω_n = 1` admits no positive composition into two
parts).

## Sources

- Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95, Theorem 1 (`integers-2026-A95-thm-1`).
