---
article_id: af_be7e1e59b977577e3c069d90
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsKCyclicPartition
---

# Is KCyclic Partition

`k`-cyclic partition of a labeled graph.

`σ` is a permutation of `V` whose total number of cycles, counting fixed points
via `σ.cycleType.card + (Fintype.card V - σ.support.card)`, equals `k`, and for
every vertex `i`, the exact truncated-cycle successor `σ^(i)(i) = j` implies
there is no directed edge from `i` to `j`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Truncated Succ](truncated-succ.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.KCyclicPartition](../../../../../sources/v2/MathlibExt.md)
- JIS statement `jis_758fa72fca5bb19057a27c73` in Gonzales, <https://cs.uwaterloo.ca/journals/JIS/VOL25/Gonzales/gonzales2.tex>, lines 345–346, SHA-256 `2d78a778c999aa0af889445a63ee690bb3a5d3ac741b6beb0b777654e1f4a627`.
