---
article_id: af_836a02b8b96f942b6970b3a6
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.fourColorTheorem
---

# Four Color Theorem

Four color theorem: no more than four colors are required to color the regions of any
planar map so that no two adjacent regions share a color, where adjacent regions share a
common boundary segment of non-zero length (modeled by `boundaryLength`: adjacency holds
iff the regions are distinct and their shared-boundary length is positive, so corner-only
point contact, of length zero, is excluded). The graph is constrained to planar maps via
`IsPlanar`; without planarity the conclusion is false (K₅ is a counterexample).
Cites stable source https://en.wikipedia.org/wiki/Four_color_theorem (statement four-color-s1).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Graph.FourColorTheoremWanted](../../../../../../sources/v2/WantedExt.md)
