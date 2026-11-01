---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.GraphicMatroid.kruskal_isForest
---

# Kruskal is Forest

Kruskal's algorithm in the form of CLRS Section 16.4: the matroid greedy algorithm on the
graphic matroid returns a forest of `G`.

## Depends on

- [Is Forest Set](is-forest-set.md)
- [Forest Oracle](forest-oracle.md)
- [Matroid Greedy](../matroid-greedy/matroid-greedy.md)

## Proof depends on

- [Forest Oracle iff](forest-oracle-iff.md)
- [Graphic Matroid](graphic-matroid.md)
- [Matroid Greedy indep](../matroid-greedy/matroid-greedy-indep.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Greedy.GraphicMatroid](../../../../../../sources/v2/CSLibExt.md)
