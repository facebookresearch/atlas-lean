---
article_id: af_a50dc89a834376cf3c021887
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.gcd_sum_eq_totient_sum
---

# Gcd Sum Totient

The gcd-sum `∑_{j=1}^n (j, n)` equals `n` times the divisor sum of `φ(d)/d`.

The source's proof groups the terms `(j, n) = e` by divisor: there are
`φ(n/e)` such terms, giving `∑_{e|n} e·φ(n/e) = n·∑_{d|n} φ(d)/d`.
Verified by exact rational arithmetic for `1 ≤ n ≤ 59`.
Proves `Wanted` entry `gcd_sum_eq_totient_sum`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.GcdSumTotient](../../../../../sources/v2/MathlibExt.md)
- Kevin A. Broughan, "The Gcd-Sum Function," Journal of Integer Sequences 4 (2001), Article 01.2.2, Theorem 2.3 (equation label 6), lines 220–226, https://cs.uwaterloo.ca/journals/JIS/VOL4/BROUGHAN/gcdsum.tex
