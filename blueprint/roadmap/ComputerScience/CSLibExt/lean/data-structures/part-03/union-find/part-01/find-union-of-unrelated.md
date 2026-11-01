---
article_id: af_6aedd7b54d1402bbb371e363
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.UnionFind.find_union_of_unrelated
---

# Find union of unrelated

Every class outside the first selected class keeps its representative:
if `z` is not equivalent to `x`, then `union` with any `y` preserves the
representative of `z` (no hypothesis on `y` is needed).

## Depends on

- [Equivalent](equivalent.md)
- [Forest](forest.md)
- [Find](find.md)
- [Union](union.md)

## Proof depends on

- [Find union](find-union.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.UnionFind](../../../../../../../../sources/v2/CSLibExt.md)
