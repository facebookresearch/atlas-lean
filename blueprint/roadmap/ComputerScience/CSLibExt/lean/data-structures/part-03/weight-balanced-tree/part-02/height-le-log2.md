---
article_id: af_3ccdfd6963c992cf752eefc7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.WeightBalancedTree.height_le_log2
---

# Height le log2

The height of a balanced tree is logarithmic in its number of keys:
`BinaryTree.height tree ≤ Nat.log2 ((tree.numNodes + 1) ^ 3) + 1`. This is the
`Nat.log2` form of `pow_height_le`, using `(4 / 3) ^ 3 > 2` to pass from
base `4 / 3` to base `2`.

## Depends on

- [Balanced](../part-01/balanced.md)

## Proof depends on

- [Pow height le](pow-height-le.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.WeightBalancedTree](../../../../../../../../sources/v2/CSLibExt.md)
