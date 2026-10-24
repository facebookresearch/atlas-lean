---
article_id: af_18315dcf4c5a7f69f4c955bd
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.cutEdge
---

# Cut Edge

Undirected edge cut, the textbook composite: reroot at `x`
(`makeRoot x`, which reverses only the root-to-`x` path and keeps every
undirected edge), then detach the subtree rooted at `y`. When `x` and `y`
are joined by an edge of a valid represented tree, the rerooting makes
`y` the root of a child subtree of `x`, so the rooted `cut y` splits the
component into the two sides of the edge `x`-`y`
(`not_connected_cutEdge`), and every other edge is retained
(`adjacent_cutEdge`); the branched-tree tests in `LinkCutTreeTests`
exhibit this on concrete forests.

The adjacency precondition is checked, not assumed: the composite runs
only when some represented tree has `x` and `y` adjacent
(`adjacentB_eq_true_iff`). Without that guard the bare composite would
cut at `y` regardless of `x` (for instance `cutEdge 99 2` on the chain
`1 → 2` would detach `2` although there is no `99`-`2` edge). When no
represented tree has the edge, `cutEdge x y` leaves the forest unchanged
(`cutEdge_eq_of_not_adjacent`); as with the other structural operations,
the preferred edges are reset either way.

## Depends on

- [State](../part-03/state.md)

## Proof depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Cut](cut.md)
- [Make Root](make-root.md)
- [Adjacent B](../part-01/adjacent-b.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
