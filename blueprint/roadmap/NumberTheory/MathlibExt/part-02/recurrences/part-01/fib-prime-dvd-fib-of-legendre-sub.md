---
article_id: af_5a1629ec5c02d3504910f6e3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.fib_prime_dvd_fib_of_legendre_sub
---

# Fibonacci Prime Divisibility

For a prime `p ≠ 5` with `p > 2`, `p` divides the Fibonacci number
`F_{p-(5/p)}`, where `(5/p)` is the Legendre symbol.

`legendreSym p 5` is `(5/p)` (`p` is the modulus); since `p ≠ 5` it is
`±1`, so the `if` selects `F_{p-1}` when `(5/p) = 1` and `F_{p+1}` when
`(5/p) = -1`, matching the source. Verified for all primes `3 ≤ p < 250`
with `p ≠ 5`.
Proves `Wanted` entry `fib_prime_dvd_fib_of_legendre_sub`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.FibonacciPrimeDivisibility](../../../../../../sources/v2/MathlibExt.md)
- Phakhinkon Phunphayap and Prapanpong Pongsriiam, "Explicit Formulas for the p-adic Valuations of Fibonomial Coefficients," Journal of Integer Sequences 21 (2018), Article 18.3.1, Lemma (label lemma2.2), item (i), lines 166–169, https://cs.uwaterloo.ca/journals/JIS/VOL21/Pongsriiam/pong12.tex
