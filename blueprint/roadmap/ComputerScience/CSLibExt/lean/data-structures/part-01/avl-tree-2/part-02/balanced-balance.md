---
article_id: af_1585442480810e4bebe267bd
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.AvlTree.balanced_balance
---

# Balanced balance

Rebalancing children whose heights differ by at most two produces a
balanced tree. This is the precondition that one insertion step maintains.

## Depends on

- [Balanced](../part-01/balanced.md)
- [Cache Correct](../part-01/cache-correct.md)
- [Tree](../part-01/tree.md)
- [Balance](../part-01/balance.md)
- [Height](../part-01/height.md)

## Proof depends on

- [Balance eq mk Node of le](balance-eq-mk-node-of-le.md)
- [Balance left double](balance-left-double.md)
- [Balance left single](balance-left-single.md)
- [Balance right double](balance-right-double.md)
- [Balance right single](balance-right-single.md)
- [Balanced mk Node](balanced-mk-node.md)
- [Mk Node](../part-01/mk-node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.AvlTree](../../../../../../../../sources/v2/CSLibExt.md)
