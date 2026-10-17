---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.card_le_card_pairs_add
---

# One round of the layered search bounds the deficit

**One round of the layered search bounds the deficit.** If no unmatched right vertex is reached
by round `k + 1`, every matching has at most as many edges as the current one plus the right
vertices first reached in round `k + 1`: the unreached left vertices and the right vertices reached
by round `k + 1` cover every edge.

## Depends on

- [Is Matching](../part-01/is-matching.md)
- [Valid](../part-01/valid.md)
- [Layers](../part-01/layers.md)
- [Pairs](../part-01/pairs.md)

## Proof depends on

- [Free](../part-01/free.md)
- [Mem layers snd of mate](../part-04/mem-layers-snd-of-mate.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
