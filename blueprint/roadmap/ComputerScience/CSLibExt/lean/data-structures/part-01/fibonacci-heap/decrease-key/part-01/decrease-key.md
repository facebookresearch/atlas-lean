---
article_id: af_73752c6ac7ea657a2b0259d7
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FibonacciHeap.decreaseKey
---

# Decrease Key

Decrease the key of the node addressed by root index `i` and path `p` to
`newKey`: cut the addressed subtree out of its tree, lower its root, and put it back
as a new tree in the root list. The cached minimum of the result is the smaller of
`newKey` and the previous cached minimum, computed without rescanning the root
list. When the address does not resolve or `newKey` is larger than the addressed
root (so the operation would be an increase), the heap is returned unchanged.
Unlike CLRS decrease-key this performs no cascading cuts: the trees carry no mark
field (see the module documentation).

## Depends on

- [Fibonacci Heap](../../../../part-02/fibonacci-heap/part-02/fibonacci-heap.md)

## Proof depends on

- [Valid](../../../../part-02/fibonacci-heap/part-01/valid-2.md)
- [Cut Tree At](cut-tree-at.md)
- [Cut Tree At elements](cut-tree-at-elements.md)
- [Cut Tree At valid](cut-tree-at-valid.md)
- [Elements](../../../../part-02/fibonacci-heap/part-01/elements-2.md)
- [Min Root](../../../../part-02/fibonacci-heap/part-02/min-root.md)
- [Min Root eq none iff](../../../../part-02/fibonacci-heap/part-02/min-root-eq-none-iff.md)
- [Elements](../../../../part-02/fibonacci-heap/part-03/elements.md)
- [Find Min](../../../../part-02/fibonacci-heap/part-03/find-min.md)
- [Find Min eq none iff](../../../../part-02/fibonacci-heap/part-03/find-min-eq-none-iff.md)
- [Find Min le](../../../../part-02/fibonacci-heap/part-03/find-min-le.md)
- [Find Min mem](../../../../part-02/fibonacci-heap/part-03/find-min-mem.md)
- [Fibonacci Tree](../../../../part-02/fibonacci-heap/part-01/fibonacci-tree.md)
- [Valid](../../../../part-02/fibonacci-heap/part-01/valid.md)
- [Decrease Root](decrease-root-2.md)
- [Cut At](cut-at.md)
- [Decrease Root](decrease-root.md)
- [Elements](../../../../part-02/fibonacci-heap/part-01/elements.md)
- [Elements decrease Root](elements-decrease-root.md)
- [Root](../../../../part-02/fibonacci-heap/part-01/root.md)
- [Root mem elements](../../../../part-02/fibonacci-heap/part-01/root-mem-elements.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FibonacciHeap.DecreaseKey](../../../../../../../../../sources/v2/CSLibExt.md)
