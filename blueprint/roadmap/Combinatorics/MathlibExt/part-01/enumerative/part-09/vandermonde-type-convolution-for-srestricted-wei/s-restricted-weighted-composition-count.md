---
article_id: af_245fa7af12d7e0fcc2d385ac
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.sRestrictedWeightedCompositionCount
---

# S Restricted Weighted Composition Count

Weighted count of `S`-restricted `f`-weighted compositions of `n` with `k` parts.

For a commutative ring `R`, a finite set `S` of nonnegative integers, and a weight
function `f : ℕ → R`, this is the sum over all tuples with every part in `S` and
total `n` of the product weight `∏ i, f (π i)`. Since every part of a composition
of `n` is at most `n`, tuples are encoded over the finite type `Fin k → Fin (n + 1)`
with parts coerced to `ℕ`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.VandermondeTypeConvolutionForSRestrictedWeightedCompositions](../../../../../../../sources/v2/MathlibExt.md)
