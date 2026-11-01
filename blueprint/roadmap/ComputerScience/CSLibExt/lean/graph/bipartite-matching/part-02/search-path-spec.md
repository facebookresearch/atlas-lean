---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.searchPath_spec
---

# Search Path spec

What `searchPath` finds is an alternating path through vertices that were neither used nor
dead.

## Depends on

- [Alt Path](../part-01/alt-path.md)
- [Valid](../part-01/valid.md)
- [Layers](../part-01/layers.md)
- [Search Path](search-path.md)

## Proof depends on

- [Free](../part-01/free.md)
- [Exists mate of mem layers](../part-01/exists-mate-of-mem-layers.md)
- [Partner Of](partner-of.md)
- [Search Path mono](search-path-mono.md)
- [Try Preds](try-preds.md)
- [Try Preds some](try-preds-some.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
