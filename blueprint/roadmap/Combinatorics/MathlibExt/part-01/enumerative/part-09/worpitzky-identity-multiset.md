---
article_id: af_42385dc321cb2b935913ca41
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.worpitzky_identity_multiset
---

# Worpitzky Multiset Identity

Worpitzky identity for multiset Eulerian numbers: for nonnegative integers
`k` over `Fin m` with total `K`, `∏ i, C (x + k i - 1) (k i)` equals
`∑ p, C (x + K - p) K * a p` where `a p` counts permutations of the multiset
`1 ^ (k 1) ⋯ m ^ (k m)` with `p - 1` descents (summed over
`Finset.Icc 1 (max 1 K)`).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.WorpitzkyMultisetIdentity](../../../../../../sources/v2/MathlibExt.md)
- A. Dzhumadil'daev and D. Yeliussizov, *Power Sums of Binomial Coefficients*, Journal of Integer Sequences 16 (2013), Article 13.1.4, Theorem Worpitzky, lines 212-217, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Yeliussizov/dzhuma6.tex>, quoting A. S. Dzhumadil'daev, *Worpitzky identity for multipermutations*, Mat. Zametki 90 (2011), 464-466.
