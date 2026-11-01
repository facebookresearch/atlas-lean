---
article_id: af_1bae20b31f77901f712c0c1e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.IntervalTree.Tree.balancedProp_rebalance_node
---

# Balanced Prop rebalance node

Rebalancing a node whose children are balanced and whose child
heights differ by at most two restores AVL balance; the resulting height
is the unrebalanced height or one less.

## Depends on

- [Cost](../part-01/cost.md)
- [Entry](../part-01/entry.md)
- [Tree](../part-01/tree.md)
- [Balanced Prop](../part-02/balanced-prop.md)
- [Rebalance With Cost](../part-02/rebalance-with-cost.md)

## Proof depends on

- [Mk Node](../part-01/mk-node.md)
- [Rotate Left](../part-02/rotate-left.md)
- [Rotate Left Right](../part-02/rotate-left-right.md)
- [Rotate Right](../part-02/rotate-right.md)
- [Rotate Right Left](../part-02/rotate-right-left.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.IntervalTree](../../../../../../../../sources/v2/CSLibExt.md)
