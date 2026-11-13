# Hybrid bound for prime divisors of $x^p - 1$

The `p`-hybrid bound (Theorem 1 for prime `n = p`). For a prime `p`, `x > 1` and
`ω_p = ω(x^p - 1)`, let `r_{i,0}` and `r_{j,1}` enumerate the primes `≢ 1` and `≡ 1 (mod p)`
(`Nat.nth`, `0`-indexed here). The source's
`x ≥ min_{0 ≤ k < ω_p} max(1 + ∏_{i ≤ k} r_{i,0}, (1 + ∏_{i ≤ k} r_{i,0} ∏_{j ≤ ω_p - k} r_{j,1})^{1/p})`
is stated equivalently as the existence of `k < ω_p` meeting both bounds, the second after
raising to the `p`-th power.

## Sources

- Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95, Proposition 2.
