---
article_id: af_701e1ab8d35f8b94a5160d26
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.completeBellPolynomial
---

# Complete Bell Polynomial

Complete Bell polynomial family `B n`, as used in source statement
`jis_4e6064ed86b521df4a4febe5` (concept `jis_sem_2f450d618ad4cc4cadb7505f`).

`B 0` is `1`, and `B (m + 1)` applied to `x : Nat → Complex` (with `x i`
standing for `y_{i+1}`) is
`∑ i ∈ Finset.range (m + 1), C(m, i) * B (m - i) x * x i`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.CompleteExponentialAutonomousFunction](../../../../../../../sources/v2/MathlibExt.md)
