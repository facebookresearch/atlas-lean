---
article_id: af_93fde52e9ddf4cfdb019e0f1
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.OrderStatisticTree.merge
---

# Merge

Merge two trees in which every key of the first is smaller than every key of
the second, repairing every rebuilt cache. The result is unspecified when that
separation does not hold.

## Depends on

- [Tree](../../../part-02/order-statistic-tree/part-01/tree.md)

## Proof depends on

- [Entry](../../../part-02/order-statistic-tree/part-01/entry.md)
- [Node](../../../part-02/order-statistic-tree/part-01/node.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.OrderStatisticTree.Delete](../../../../../../../../sources/v2/CSLibExt.md)
