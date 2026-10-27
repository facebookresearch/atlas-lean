---
article_id: af_0ecea5ebfdd1f6f7a248be4c
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.axler_nth_prime_upper_bound
---

# Axler Nth Prime Upper Bound Wanted

Christian Axler's upper bound for the `n`th prime (statement only).

For one-indexed `n ≥ 46254381`, with `pₙ` the `n`th prime,
`pₙ < n * (log n + log log n - 1 + (log log n - 2) / log n -
  ((log log n) ^ 2 - 6 * log log n + 10.667) / (2 * (log n) ^ 2))`.

Mathlib's `Nat.nth Nat.Prime` is zero-indexed, so `Nat.nth Nat.Prime (n - 1)`
is the source's one-indexed `pₙ`; the lower bound on `n` makes this
subtraction safe. The decimal `10.667` is kept exact as Lean's decimal
rational literal coerced to `ℝ`. This exact refinement is due to
Christian Axler, not to Rosser–Schoenfeld.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.PrimeCounting.AxlerNthPrimeUpperBoundWanted](../../../../../../sources/v2/WantedExt.md)
- Christian Axler, "New Estimates for the nth Prime Number," Journal of Integer Sequences 22 (2019), Article 19.4.2, Theorem `thm101`, equation (1.12), lines 160–166 of https://cs.uwaterloo.ca/journals/JIS/VOL22/Axler/axler17.tex. Context at lines 148–158 distinguishes this refinement from the weaker earlier Dusart bound.
