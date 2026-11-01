---
article_id: af_0b2c1111c8af4204c9da170b
declaration: theorem
origin: cited
statement: formalized
lean: SpaceFillingCurve.space_filling_curve_heuristic
---

# Lemma 9.6.9 (Space-filling curve heuristic)

Let $x_1, \ldots, x_n \in [0,1]^2$. There is a permutation $\sigma$ of $[n]$ with (indices taken mod $n$) $\sum_{i=1}^{n} |x_{\sigma(i)} - x_{\sigma(i+1)}|^2 = O(1)$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 9.6.7](168-theorem-9-6-7.md)

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 9, Section 9.6](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
