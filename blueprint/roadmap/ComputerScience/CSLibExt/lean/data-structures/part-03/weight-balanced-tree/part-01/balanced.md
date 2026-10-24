---
article_id: af_696ae512e38acbf19e87d0b5
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.WeightBalancedTree.Balanced
---

# Balanced

The weight-balance invariant `BB[1/4]`: at every node, each child has
weight at most three quarters of the weight of the node,
`4 * weight child ≤ 3 * weight node`, written out in key counts as
`4 * (child.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2)`.
See `balanced_node_iff_weight` for the same statement using `weight`.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.WeightBalancedTree](../../../../../../../../sources/v2/CSLibExt.md)
