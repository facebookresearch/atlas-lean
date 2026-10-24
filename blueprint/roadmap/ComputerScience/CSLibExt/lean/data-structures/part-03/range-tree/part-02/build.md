---
article_id: af_4ee4afe3529adff5040fd79a
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.RangeTree.build
---

# Build

Builds a balanced range tree from a list by recursively splitting in
half, caching each node's leaf interval from its (once-built) children.
The input order is preserved verbatim (see `toList_build`); sortedness is
a hypothesis on the caller, recorded by `valid_build_of_sorted`.

## Depends on

- [Range Tree](../part-01/range-tree.md)

## Proof depends on

- [Tmax](../part-01/tmax.md)
- [Tmin](../part-01/tmin.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.RangeTree](../../../../../../../../sources/v2/CSLibExt.md)
