---
article_id: af_1eb4a04b12ee77693caf04f1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.WeightBalancedTree.balanced_node_iff_weight
---

# Balanced node iff weight

The node case of `Balanced`, stated with `weight`: a node is balanced
exactly when its children are balanced and each child has weight at most
three quarters of the weight of the node. This is the classical
`BB[1/4]` invariant.

## Depends on

- [Balanced](balanced.md)
- [Weight](weight.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.WeightBalancedTree](../../../../../../../../sources/v2/CSLibExt.md)
