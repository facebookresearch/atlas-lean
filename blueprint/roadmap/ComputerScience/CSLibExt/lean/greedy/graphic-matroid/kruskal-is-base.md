---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.GraphicMatroid.kruskal_isBase
---

# Kruskal is Base

If the order lists exactly the edges of `G`, the result is a maximal forest of `G` (a base of
the graphic matroid).

## Depends on

- [Forest Oracle](forest-oracle.md)
- [Graphic Matroid](graphic-matroid.md)
- [Matroid Greedy](../matroid-greedy/matroid-greedy.md)

## Proof depends on

- [Forest Oracle iff](forest-oracle-iff.md)
- [Matroid Greedy is Base](../matroid-greedy/matroid-greedy-is-base.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Greedy.GraphicMatroid](../../../../../../sources/v2/CSLibExt.md)
