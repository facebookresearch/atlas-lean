---
article_id: af_03d135eeb742f391d05b57bc
declaration: def
origin: cited
statement: formalized
lean: PermutationStability.IsAlmostHomomorphism
---

# Is Almost Homomorphism

A sequence of (arbitrary) set maps `f n : G → Equiv.Perm (Fin n)` is an
almost-homomorphism when the normalized Hamming defect
`d(f n g * f n h, f n (g * h))` tends to zero for every pair `g h`.
Following the source, no condition such as `f n 1 = 1` is imposed.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Normalized Hamming Distance](normalized-hamming-distance.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.PermutationStability](../../../../../sources/v2/MathlibExt.md)
