---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.searchPath_dead
---

# Dead vertices have no escape

**Dead vertices have no escape.** Every right vertex that a search from a vertex first reached
in round `k + 1` newly marks dead has no shortest escape avoiding the used left vertices and the
final dead set: Hopcroft and Karp's pruning loses no path.

## Depends on

- [Exact Level](exact-level.md)
- [No Escape](no-escape.md)
- [Valid](../part-01/valid.md)
- [Search Path](../part-02/search-path.md)

## Proof depends on

- [Partner](partner.md)
- [Free](../part-01/free.md)
- [Is Chain From](is-chain-from.md)
- [Layers](../part-01/layers.md)
- [Mem layers length](../part-03/mem-layers-length.md)
- [Partner Of](../part-02/partner-of.md)
- [Search Path mono](../part-02/search-path-mono.md)
- [Search Path none marks](search-path-none-marks.md)
- [Try Preds](../part-02/try-preds.md)
- [Try Preds dead](try-preds-dead.md)
- [Try Preds none](try-preds-none.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
