---
article_id: af_7968f610d8339d2262e6761c
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FibonacciHeap.deleteMin
---

# Delete Min

Remove and return the minimum value. The children of the minimum tree become roots
and the root list is consolidated; the new cached minimum is the minimum root of the
consolidated forest.

## Depends on

- [Fibonacci Heap](../part-02/fibonacci-heap.md)

## Proof depends on

- [Valid](../part-01/valid-2.md)
- [Sublist](../part-02/sublist.md)
- [Consolidate](../part-02/consolidate.md)
- [Elements](../part-01/elements-2.md)
- [Min Root](../part-02/min-root.md)
- [Remove Min Tree](../part-02/remove-min-tree.md)
- [Remove Min Tree spec](../part-02/remove-min-tree-spec.md)
- [Valid append](../part-02/valid-append.md)
- [Valid consolidate](../part-02/valid-consolidate.md)
- [Fibonacci Tree](../part-01/fibonacci-tree.md)
- [Valid](../part-01/valid.md)
- [Child valid](../part-01/child-valid.md)
- [Children](../part-01/children.md)
- [Elements](../part-01/elements.md)
- [Root](../part-01/root.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FibonacciHeap](../../../../../../../../sources/v2/CSLibExt.md)
