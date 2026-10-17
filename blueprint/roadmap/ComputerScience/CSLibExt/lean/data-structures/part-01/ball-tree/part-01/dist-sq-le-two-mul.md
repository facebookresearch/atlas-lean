---
article_id: af_36c3aba0f87eb4e7af97c533
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BallTree.distSq_le_two_mul
---

# Dist Sq le two mul

A weak triangle inequality for squared distance, with the factor `2`
coming from `(x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2)` coordinatewise. This is
the estimate that makes bounding-sphere pruning sound without square
roots.

## Depends on

- [Dist Sq](dist-sq.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BallTree](../../../../../../../../sources/v2/CSLibExt.md)
