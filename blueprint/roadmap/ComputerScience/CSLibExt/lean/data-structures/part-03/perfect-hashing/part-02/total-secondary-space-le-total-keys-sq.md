---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.PerfectHashing.totalSecondarySpace_le_totalKeys_sq
---

# Total Secondary Space le total Keys sq

Elementary space bound under the FKS sizing rule: the total secondary space
`∑ i, nᵢ²` is at most `(∑ i, nᵢ)²`, the square of the total number of keys. The
linear bound `∑ i, nᵢ² = O(n)` of FKS additionally requires a good primary hash
function, whose existence is a probabilistic statement not proved here.

## Depends on

- [Perfect Hashing](../part-01/perfect-hashing.md)
- [Square Sized](square-sized.md)
- [Total Keys](total-keys.md)
- [Total Secondary Space](total-secondary-space.md)

## Proof depends on

- [Bucket Size](../part-01/bucket-size.md)
- [Total Secondary Space eq sum sq](total-secondary-space-eq-sum-sq.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.PerfectHashing](../../../../../../../../sources/v2/CSLibExt.md)
