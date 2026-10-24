---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.phaseAux_maximal
---

# Phase Aux maximal

The invariant of a phase: a shortest chain from `j` (first reached in round `d + 1`) that avoids
the earlier paths `F` and the paths found from the candidates `js` cannot exist while `j` is still
a candidate or dead.

## Depends on

- [Exact Level](exact-level.md)
- [Is Chain From](is-chain-from.md)
- [No Escape](no-escape.md)
- [Valid](../part-01/valid.md)
- [Phase Aux](../part-03/phase-aux.md)

## Proof depends on

- [Alt Path](../part-01/alt-path.md)
- [Free](../part-01/free.md)
- [Layers](../part-01/layers.md)
- [Mark L](../part-02/mark-l.md)
- [Mark R](../part-03/mark-r.md)
- [Not dead of chain](not-dead-of-chain.md)
- [Search Path](../part-02/search-path.md)
- [Dead vertices have no escape](search-path-dead.md)
- [Search Path mono](../part-02/search-path-mono.md)
- [Search Path none marks](search-path-none-marks.md)
- [Search Path spec](../part-02/search-path-spec.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
