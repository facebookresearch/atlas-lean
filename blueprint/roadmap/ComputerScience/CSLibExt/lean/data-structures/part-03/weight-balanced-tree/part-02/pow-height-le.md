---
article_id: af_cfb468da925951cd691b8dc0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.WeightBalancedTree.pow_height_le
---

# Pow height le

The weight of a balanced tree grows at least geometrically in its
height with ratio `4 / 3`: a balanced tree of height `k + 1` has weight
at least `(4 / 3) ^ k`, in integer form `4 ^ k ≤ 3 ^ k * weight tree`.
This is where the weight form of the invariant is used: the taller child
has weight at most three quarters of the weight of the node.

## Depends on

- [Balanced](../part-01/balanced.md)
- [Weight](../part-01/weight.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.WeightBalancedTree](../../../../../../../../sources/v2/CSLibExt.md)
