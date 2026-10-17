---
article_id: af_95c8a916349c7226ab0e3104
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FibonacciTree.cutAt
---

# Cut At

Cut out the subtree at a path: returns the extracted subtree together with the
remainder of the tree with ancestors rebuilt and degrees corrected. The remainder is
`none` exactly for the empty path, where the whole tree is extracted.

## Depends on

- [Fibonacci Tree](../../../../part-02/fibonacci-heap/part-01/fibonacci-tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FibonacciHeap.DecreaseKey](../../../../../../../../../sources/v2/CSLibExt.md)
