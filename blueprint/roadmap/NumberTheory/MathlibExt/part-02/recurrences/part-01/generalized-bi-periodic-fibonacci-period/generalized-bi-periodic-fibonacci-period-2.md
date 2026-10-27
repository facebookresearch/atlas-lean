---
article_id: af_b9affb183f17ab1e53679511
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generalizedBiPeriodicFibonacci_period_dvd
---

# Generalized Bi Periodic Fibonacci period dvd

Pisano-period prime divisor bound for the generalized bi-periodic Fibonacci
sequence when the discriminant is a nonzero quadratic residue.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Generalized Bi Periodic Fibonacci period dvd general](generalized-bi-periodic-fibonacci-period.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.GeneralizedBiPeriodicFibonacciPeriod](../../../../../../../sources/v2/MathlibExt.md)
- Hacène Belbachir and Celia Salhi, "The Generalized Bi-Periodic Fibonacci Sequence Modulo m," Journal of Integer Sequences 24 (2021), Article 21.9.4, Theorem (label th1), lines 225–226, <https://cs.uwaterloo.ca/journals/JIS/VOL24/Salhi/salhi4.tex>. It follows from `generalizedBiPeriodicFibonacci_period_dvd_general`, which drops the unused `IsSquare Δ`. Proves `Wanted` entry `generalizedBiPeriodicFibonacci_period_dvd`.
