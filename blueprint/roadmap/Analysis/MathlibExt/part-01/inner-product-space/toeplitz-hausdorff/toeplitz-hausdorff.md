---
article_id: af_383436759d27c44866ee4211
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorffWanted.toeplitz_hausdorff
---

# Toeplitz hausdorff

The numerical range of a bounded operator on a complex Hilbert space is convex.

## Depends on

- [Numerical Range](numerical-range.md)

## Proof depends on

- [Toeplitz hausdorff general](toeplitz-hausdorff-general.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorff](../../../../../../sources/v2/MathlibExt.md)
- O. Toeplitz, Das algebraische Analogon zu einem Satze von Fejer, Math. Z. 2 (1918), 187-197, DOI 10.1007/BF01212904; F. Hausdorff, Der Wertvorrat einer Bilinearform, Math. Z. 3 (1919), 314-316, DOI 10.1007/BF01292610. It follows from `toeplitz_hausdorff_general`; the hypothesis `CompleteSpace E` is unused and keeps the source's shape.
