---
article_id: af_c342e7fe0ed1e605ba049623
declaration: def
origin: cited
statement: formalized
lean: Polynomial.IsKComplete
---

# Is KComplete

A polynomial `f` over a finite field is complete to level `k`
(`k`-complete) when `f + i * X` is a permutation polynomial for every natural
index `i ≤ k`, with `i` cast into `F`. The source assumes positive `k`; the
predicate is stated for all natural levels, with the positive-level
characterization `isKComplete_succ_iff` and the zero-level boundary
`isKComplete_zero` below.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Permutation Polynomial](is-permutation-polynomial.md)

## Sources

- [MathlibExt, MathlibExt.FieldTheory.Finite.PermutationPolynomial](../../../../../sources/v2/MathlibExt.md)
