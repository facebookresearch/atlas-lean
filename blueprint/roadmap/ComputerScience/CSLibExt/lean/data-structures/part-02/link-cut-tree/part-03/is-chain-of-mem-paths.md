---
article_id: af_ddd021198bd7b652e431e5d2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.LinkCutTree.State.isChain_of_mem_paths
---

# Is Chain of mem paths

Every preferred path is a genuine path of the represented forest:
consecutive vertices are joined by a parent-child edge of one represented
tree (`isChain_of_mem_treePaths`). This holds for every state, with no
validity hypothesis.

## Depends on

- [Tree](../../euler-tour-tree/part-01/tree.md)
- [Adjacent](../part-01/adjacent.md)
- [State](state.md)
- [Paths](paths.md)

## Proof depends on

- [Is Chain of mem tree Paths](is-chain-of-mem-tree-paths.md)
- [Tree Paths](tree-paths.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree](../../../../../../../../sources/v2/CSLibExt.md)
