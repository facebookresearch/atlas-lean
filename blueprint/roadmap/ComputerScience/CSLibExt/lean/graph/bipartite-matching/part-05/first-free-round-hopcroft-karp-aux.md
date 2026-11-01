---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.firstFreeRound_hopcroftKarpAux
---

# Each phase lengthens the shortest augmenting paths

**Each phase lengthens the shortest augmenting paths.** After `f` phases from a matching whose
`firstFreeRound` is at least `c`, the `firstFreeRound` is at least `c + f` (or there is none).

## Depends on

- [Valid](../part-01/valid.md)
- [First Free Round](../part-03/first-free-round.md)
- [Hopcroft Karp Aux](../part-03/hopcroft-karp-aux.md)

## Proof depends on

- [First Free Round eq none](../part-03/first-free-round-eq-none.md)
- [Flip](../part-01/flip.md)
- [Hk Step](../part-03/hk-step.md)
- [Hk Step none](../part-03/hk-step-none.md)
- [Hk Step some](../part-03/hk-step-some.md)
- [Hopcroft Karp Aux of hk Step none](hopcroft-karp-aux-of-hk-step-none.md)
- [Layers](../part-01/layers.md)
- [The next phase's paths are strictly longer](lt-first-free-round-flip-phase.md)
- [Matched](../part-01/matched.md)
- [Phase](../part-03/phase.md)
- [Phase Aux](../part-03/phase-aux.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
