---
article_id: af_cfa46bfb9a9f3076e3222cc1
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.axler_nth_prime_lower_bound
---

# Axler Nth Prime Lower Bound Wanted

Axler's explicit lower bound for the `n`th prime (statement only).

For every integer `n ≥ 2`,
`pₙ > n * (log n + log log n - 1 + (log log n - 2) / log n -
((log log n) ^ 2 - 6 * log log n + 11.321) / (2 * (log n) ^ 2))`.

Mathlib's `Nat.nth Nat.Prime` is zero-indexed, so `Nat.nth Nat.Prime (n - 1)`
is the source's one-indexed `pₙ`; the hypothesis `2 ≤ n` makes the
subtraction `n - 1` safe. The inequality is strict and the decimal `11.321`
is kept exactly as stated.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.PrimeCounting.AxlerNthPrimeLowerBoundWanted](../../../../../../sources/v2/WantedExt.md)
- Christian Axler, "New Estimates for the nth Prime Number," Journal of Integer Sequences 22 (2019), Article 19.4.2, Theorem `thm104`, equation (1.14), lines 190--196 of https://cs.uwaterloo.ca/journals/JIS/VOL22/Axler/axler17.tex.
