---
article_id: af_b3564ab990dc54c7717a4d11
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.UnionFind.unionWithCost
---

# Union With Cost

Run `union`, charging its two root searches and, only when the two
representatives are distinct, one root-link operation; when they already
coincide, `union` performs no link and none is charged.

## Depends on

- [Forest](forest.md)

## Proof depends on

- [Find](find.md)
- [Find With Cost](find-with-cost.md)
- [Union](union.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.UnionFind](../../../../../../../../sources/v2/CSLibExt.md)
