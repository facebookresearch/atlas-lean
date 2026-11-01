---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.mul_card_sub_le
---

# The deficit is at most `b / d`

**The deficit is at most `b / d`** (the counting step of Hopcroft and Karp's bound): if no
unmatched right vertex is reached in the first `d` rounds, then `d` times the deficit of the
current matching against any matching is at most the number of right vertices reached by round
`d`.

## Depends on

- [Is Matching](../part-01/is-matching.md)
- [Valid](../part-01/valid.md)
- [Layers](../part-01/layers.md)
- [Pairs](../part-01/pairs.md)

## Proof depends on

- [One round of the layered search bounds the deficit](card-le-card-pairs-add.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
