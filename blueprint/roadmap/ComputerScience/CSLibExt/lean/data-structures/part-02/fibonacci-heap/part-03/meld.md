---
article_id: af_459fc62534ee4973dca1b3b9
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FibonacciHeap.meld
---

# Meld

Meld two Fibonacci heaps: concatenate the root lists and keep the smaller cached
minimum. No linking happens until the next minimum deletion.

## Depends on

- [Fibonacci Heap](../part-02/fibonacci-heap.md)

## Proof depends on

- [Valid](../part-01/valid-2.md)
- [Min Option](../part-02/min-option.md)
- [Min Root](../part-02/min-root.md)
- [Min Root append](../part-02/min-root-append.md)
- [Valid append](../part-02/valid-append.md)
- [Fibonacci Tree](../part-01/fibonacci-tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FibonacciHeap](../../../../../../../../sources/v2/CSLibExt.md)
