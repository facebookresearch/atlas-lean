---
article_id: af_428d9e2e569349ce9a2c8105
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.mandl_prime_sum_inequality
---

# Mandl Prime Sum Wanted

Mandl's inequality for the sum of the first `n` primes (statement only).

For every `n ≥ 9`, twice the sum of the first `n` primes is at most `n`
times the `n`th prime. The source's one-indexed primes `p₁, …, pₙ` become
zero-indexed `Nat.nth Nat.Prime 0, …, Nat.nth Nat.Prime (n - 1)`, and the
denominator in Mandl's inequality is cleared.

Dusart proved the inequality for every `n ≥ 9`, as quoted by Axler.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.PrimeCounting.MandlPrimeSumWanted](../../../../../../sources/v2/WantedExt.md)
- Christian Axler, "On a Sequence Involving Prime Numbers," Journal of Integer Sequences 18 (2015), source equation (101), lines 89-107, https://cs.uwaterloo.ca/journals/JIS/VOL18/Axler/axler6.tex. Complete-source SHA-256 d14106761bbab2548473a1d8321e1a79953158fe2e3c36551926473c3851c14b; raw lines 89-107 joined with LF and no terminal LF SHA-256 cf4e5fb018d3b12e931f0527d0262598e3186bcd26654762946952009b961479.
