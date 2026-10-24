---
article_id: af_0c8b5d4258062cabbdd8a91b
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BallTree.build
---

# Build

Builds a ball tree by recursive halving: the center is the first point,
the bound is `radiusSq` over the whole list, and the children are built
from the two halves of the list.

## Depends on

- [Ball Tree](ball-tree.md)

## Proof depends on

- [Radius Sq](radius-sq.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BallTree](../../../../../../../../sources/v2/CSLibExt.md)
