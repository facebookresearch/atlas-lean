---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.card_le_hopcroftKarpAux_sqrt
---

# Hopcroft and Karp's bound: `2 ⌊√b⌋ + 2` phases suffice

**Hopcroft and Karp's bound: `2 ⌊√b⌋ + 2` phases suffice.** From the empty matching, after
`2 ⌊√b⌋ + 2` phases the matching is maximum. After the first `⌊√b⌋ + 1` phases every augmenting
path has more than `⌊√b⌋` pairs (`firstFreeRound_hopcroftKarpAux`), so the deficit is at most
`⌊√b⌋` (`mul_card_sub_le`), and each further phase adds an edge.

## Depends on

- [Is Matching](../part-01/is-matching.md)
- [Hopcroft Karp Aux](../part-03/hopcroft-karp-aux.md)
- [Pairs](../part-01/pairs.md)

## Proof depends on

- [Valid](../part-01/valid.md)
- [Card le hopcroft Karp Aux of le](card-le-hopcroft-karp-aux-of-le.md)
- [Kőnig's certificate](../part-02/card-le-of-no-free.md)
- [First Free Round](../part-03/first-free-round.md)
- [First Free Round eq none](../part-03/first-free-round-eq-none.md)
- [First Free Round eq some](../part-03/first-free-round-eq-some.md)
- [Each phase lengthens the shortest augmenting paths](first-free-round-hopcroft-karp-aux.md)
- [Hopcroft Karp Aux add](hopcroft-karp-aux-add.md)
- [Layers](../part-01/layers.md)
- [The deficit is at most `b / d`](mul-card-sub-le.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
