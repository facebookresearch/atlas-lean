---
article_id: af_c968710f42922781bb2901a4
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.completeExponentialAutonomousFunction
---

# Complete Exponential Autonomous Function

N-th complete exponential autonomous function of order `k` (`k ≥ 1`), with
parameter `a : Complex` and variables `x = (x₁, …, xₖ)`, as specified in source
statement `jis_4e6064ed86b521df4a4febe5` (concept `jis_sem_2f450d618ad4cc4cadb7505f`).

Initial values: `f 0 = x 0` through `f (k - 1) = x (k - 1)`, `f k = a * exp (x 0)`.
Recurrence: for `n > k`, with `m = n - k ≥ 1`,
`f n = a * exp (x 0) * B m (f 1, …, f m)`, where `B` is the complete Bell
polynomial family `completeBellPolynomial` (argument `i : Nat` standing for
`f (i + 1)`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Complete Bell Polynomial](complete-bell-polynomial.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.CompleteExponentialAutonomousFunction](../../../../../../../sources/v2/MathlibExt.md)
