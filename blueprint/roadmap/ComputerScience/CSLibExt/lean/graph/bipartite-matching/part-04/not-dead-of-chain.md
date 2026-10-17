---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.BipartiteMatching.not_dead_of_chain
---

# Not dead of chain

Along a shortest chain that avoids the vertices of earlier paths, a dead set whose members are
on earlier paths or have no escape contains no right vertex of the chain.

## Depends on

- [Exact Level](exact-level.md)
- [Is Chain From](is-chain-from.md)
- [No Escape](no-escape.md)

## Proof depends on

- [Tail](tail.md)
- [Free](../part-01/free.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.BipartiteMatching](../../../../../../../sources/v2/CSLibExt.md)
