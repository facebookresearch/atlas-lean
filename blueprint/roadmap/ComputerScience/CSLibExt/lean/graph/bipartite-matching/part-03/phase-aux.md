---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.phaseAux
---

# Phase Aux

Search from each listed right vertex in turn through the vertices not yet used, collecting the
paths found; each path's vertices become used, and right vertices from which a search failed stay
dead.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Mark L](../part-02/mark-l.md)
- [Mark R](mark-r.md)
- [Search Path](../part-02/search-path.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
