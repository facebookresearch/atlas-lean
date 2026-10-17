---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.card_le_hopcroftKarpAux_of_le
---

# Card le hopcroft Karp Aux of le

Each phase adds an edge until the matching is maximum: if the current matching is within `f`
of a matching `M`, then `f` more phases reach at least `M`'s size.

## Depends on

- [Is Matching](../part-01/is-matching.md)
- [Valid](../part-01/valid.md)
- [Hopcroft Karp Aux](../part-03/hopcroft-karp-aux.md)
- [Pairs](../part-01/pairs.md)

## Proof depends on

- [Kőnig's certificate](../part-02/card-le-of-no-free.md)
- [Card pairs](../part-02/card-pairs.md)
- [Hk Step](../part-03/hk-step.md)
- [Hk Step none](../part-03/hk-step-none.md)
- [Hk Step some](../part-03/hk-step-some.md)
- [Hopcroft Karp Aux of hk Step none](hopcroft-karp-aux-of-hk-step-none.md)
- [Matched](../part-01/matched.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
