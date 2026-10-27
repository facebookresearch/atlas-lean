---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.DepthFirstSearch.dfsAll_exact_steps
---

# Dfs All exact steps

Whole-graph DFS has exactly two transitions per vertex plus one per adjacency entry,
including repeated entries and self-loops.

## Depends on

- [Traversal](../depth-first-search/part-01/traversal.md)
- [Dfs All](../depth-first-search/part-02/dfs-all.md)
- [Directed Adjacency](../directed-adjacency-2/part-01/directed-adjacency.md)

## Proof depends on

- [Dfs](../depth-first-search/part-01/dfs.md)
- [Dfs exact steps](dfs-exact-steps.md)
- [Mem dfs All preorder](../depth-first-search/part-02/mem-dfs-all-preorder.md)
- [Preorder nodup](../depth-first-search/part-01/preorder-nodup.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.DepthFirstSearchCosts](../../../../../../sources/v2/CSLibExt.md)
