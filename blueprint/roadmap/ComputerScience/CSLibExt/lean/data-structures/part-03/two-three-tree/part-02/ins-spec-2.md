---
article_id: af_8cccf0b9ae271627893c13b5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TwoThreeTree.ins_spec
---

# Ins spec

Insertion into an ordered tree satisfies `InsSpec`: it preserves the
ordering invariant and its flattening is `orderedInsert` of the old flattening.
Balance is automatic from the height index.

## Depends on

- [Ins Spec](ins-spec.md)
- [Ordered](../part-01/ordered.md)
- [Tree](../part-01/tree.md)
- [Ins](../part-01/ins.md)

## Proof depends on

- [All](../part-01/all.md)
- [Overflow](../part-01/overflow.md)
- [All iff forall flatten](../part-01/all-iff-forall-flatten.md)
- [Flatten](../part-01/flatten.md)
- [Flatten Aux](../part-01/flatten-aux.md)
- [Ordered Insert](../../../part-02/ordered-insert/ordered-insert.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.TwoThreeTree](../../../../../../../../sources/v2/CSLibExt.md)
