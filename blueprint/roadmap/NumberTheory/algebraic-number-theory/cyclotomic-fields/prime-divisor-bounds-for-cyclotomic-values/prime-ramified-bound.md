# Ramified bound on prime divisors of $x^p - 1$ for prime $p$

The `p`-ramified bound (Theorem 2 for prime `n = p`). For a prime `p`, `x > 1` and
`ω_p = ω(x^p - 1)`, let `r_{i,0}` and `r_{j,1}` enumerate the primes `≢ 1` and `≡ 1 (mod p)`
(`Nat.nth`, `0`-indexed here), `p = r_{b,0}`, `R^0_k = ∏_{i < k} r_{i,0}` and
`R^1_k = ∏_{j < ω_p - k} r_{j,1}`. The source's minima over `k ∈ [0, k') ∪ [k', ω_p)` (with
`k' = b + 1`) are stated as the existence of `k < ω_p` meeting both bounds, the second after
raising to the `p`-th power; `p^{-1} R^0_{k+1}` is written as the product over
`{0, …, k} \ {b}`. If `p ∤ x^p - 1`: `k ≤ b` gives `1 + R^0_k ≤ x`, `1 + R^0_k R^1_k ≤ x^p`, and
`k > b` gives `1 + p^{-1} R^0_{k+1} ≤ x`, `1 + p^{-1} R^0_{k+1} R^1_k ≤ x^p`. If `p ∣ x^p - 1`:
`k ≤ b` gives `1 + p R^0_{k-1} ≤ x`, `1 + p^2 R^0_{k-1} R^1_k ≤ x^p`, and `k > b` gives
`1 + R^0_k ≤ x`, `1 + p R^0_k R^1_k ≤ x^p`. The divisible case requires `p ≠ 2` and has `k > 0`:
`R^0_{-1}` is undefined at `k = 0`, and for `p = 2`, `x = 3` (`x^2 - 1 = 8`, `ω_2 = 1`) the only
admitted `k = 0` fails under any reading (with `R^0_{-1} := 1` the second bound reads
`1 + 4 · 3 = 13 ≤ 9`).

## Sources

- Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95, Proposition 3 (`integers-2026-A95-prop-3`).
