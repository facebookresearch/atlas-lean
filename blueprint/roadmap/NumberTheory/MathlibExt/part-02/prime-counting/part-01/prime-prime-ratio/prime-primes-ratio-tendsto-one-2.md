---
article_id: af_f1cf03c9646455decf376776
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.primePrimes_ratio_tendsto_one
---

# Prime Primes ratio tendsto one

For the prime-primes `q n = Nat.nth Nat.Prime (Nat.nth Nat.Prime n)`
(prime-indexed primes, `q_n ~ n * log^2 n`), consecutive ratios tend to one:
`(q n : ℝ) / q (n + 1) → 1`.

The corollary follows from the Rosser–Schoenfeld bounds of the theorem;
parts (a)–(b) give `q_n ~ n log^2 n`. This states only part (c), the
consecutive-ratio limit. `Nat.nth Nat.Prime` needs the infinitude of primes,
supplied as the `Infinite` instance hypothesis.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Prime Primes ratio tendsto one'](prime-primes-ratio-tendsto-one.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.PrimePrimeRatio](../../../../../../../sources/v2/MathlibExt.md)
- Kevin A. Broughan and A. Ross Barnett, "On the Subsequence of Primes Having Prime Subscripts," Journal of Integer Sequences 12 (2009), Article 09.2.3, Corollary to the Theorem (label thm:bounds), part (c), lines 193–199, https://cs.uwaterloo.ca/journals/JIS/VOL12/Broughan/broughan16.tex
