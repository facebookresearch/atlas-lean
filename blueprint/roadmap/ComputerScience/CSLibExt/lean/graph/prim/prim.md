---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.Prim.prim
---

# Basic

Prim's source-order indexed-heap procedure, returning parents and same-run event counts.
The five heap coordinates count comparisons, swaps, inverse reads, inverse writes and
entry append/pop/replacement;
the two scalar coordinates count adjacency inspections and successful membership tests.
Disconnected inputs still extract all vertices and return a parent forest.

## Depends on

- [Directed Adjacency](../directed-adjacency-2/part-01/directed-adjacency.md)

## Proof depends on

- [Indexed Min Queue](../../data-structures/part-01/indexed-min-queue/basic/indexed-min-queue.md)
- [Decrease Key](../../data-structures/part-01/indexed-min-queue/basic/decrease-key.md)
- [Empty](../../data-structures/part-01/indexed-min-queue/basic/empty.md)
- [Extract Min](../../data-structures/part-01/indexed-min-queue/basic/extract-min.md)
- [Insert](../../data-structures/part-01/indexed-min-queue/basic/insert.md)
- [Member](../../data-structures/part-01/indexed-min-queue/basic/member.md)
- [Position valid](../../data-structures/part-01/indexed-min-queue/correctness/position-valid.md)
- [Min Heap](../../data-structures/part-02/binary-heap/part-02/min-heap.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.Prim.Basic](../../../../../../sources/v2/CSLibExt.md)
