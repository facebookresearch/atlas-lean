---
article_id: af_66afd37b9bb91b6f4cc3a6a3
declaration: def
origin: cited
statement: formalized
lean: PermutationStability.normalizedHammingDistance
---

# Normalized Hamming Distance

Normalized Hamming distance between two permutations of `Fin n`: the
fraction of points on which they disagree. At `n = 0` the denominator is zero,
so the quotient is `0` by the `ZeroInv₀` convention; this single value is
harmless for `Filter.atTop` convergence statements.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.GroupTheory.PermutationStability](../../../../../sources/v2/MathlibExt.md)
