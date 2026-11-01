---
article_id: af_8f2d431c4028256489d91825
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.WeightBalancedTree.balance
---

# Balance

Rebuild a node from children that violate the weight invariant by at most
one inserted key, restoring balance. When the left child is too heavy, a
single right rotation is performed if the left-right grandchild is at most
twice as large as the left-left one, and a double left-right rotation
otherwise; the right-heavy case is symmetric. Children that already satisfy
the invariant are rebuilt without rotation.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.WeightBalancedTree](../../../../../../../../sources/v2/CSLibExt.md)
