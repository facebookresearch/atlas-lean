---
article_id: af_bdb5b5f68cc4ec893a4a7dc3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.FibonacciTree.Valid.decreaseRoot
---

# Decrease Root

Lowering the root of a valid tree to a key no larger than the old root keeps the
tree valid: the new root is still no greater than every represented element.

## Depends on

- [Fibonacci Tree](../../../../part-02/fibonacci-heap/part-01/fibonacci-tree.md)
- [Valid](../../../../part-02/fibonacci-heap/part-01/valid.md)
- [Decrease Root](decrease-root.md)
- [Root](../../../../part-02/fibonacci-heap/part-01/root.md)

## Proof depends on

- [Child valid](../../../../part-02/fibonacci-heap/part-01/child-valid.md)
- [Degree eq](../../../../part-02/fibonacci-heap/part-01/degree-eq.md)
- [Root le](../../../../part-02/fibonacci-heap/part-01/root-le.md)
- [Elements](../../../../part-02/fibonacci-heap/part-01/elements.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FibonacciHeap.DecreaseKey](../../../../../../../../../sources/v2/CSLibExt.md)
