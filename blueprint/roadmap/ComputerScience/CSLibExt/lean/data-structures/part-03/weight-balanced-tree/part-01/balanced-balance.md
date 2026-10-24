---
article_id: af_4bafa40427fe9338d07b9178
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.WeightBalancedTree.balanced_balance
---

# Balanced balance

Rebalancing children that violate the weight invariant by at most the
one-key weight slack
`4 * (child.numNodes + 1) ≤ 3 * (left.numNodes + right.numNodes + 2) + 1`
produces a balanced tree. This is the precondition that one insertion
step maintains.

## Depends on

- [Balanced](balanced.md)
- [Balance](balance.md)

## Proof depends on

- [Balanced node](balanced-node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.WeightBalancedTree](../../../../../../../../sources/v2/CSLibExt.md)
