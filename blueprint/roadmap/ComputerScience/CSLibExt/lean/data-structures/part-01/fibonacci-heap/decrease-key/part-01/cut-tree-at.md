---
article_id: af_78db1528743fe5cab7d140c3
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FibonacciForest.cutTreeAt
---

# Cut Tree At

Cut the subtree at path `p` inside the `i`-th tree of a forest: returns the
extracted subtree together with the forest in which that tree is replaced by the cut
remainder (or removed when the whole tree was extracted).

## Depends on

- [Fibonacci Tree](../../../../part-02/fibonacci-heap/part-01/fibonacci-tree.md)

## Proof depends on

- [Cut At](cut-at.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FibonacciHeap.DecreaseKey](../../../../../../../../../sources/v2/CSLibExt.md)
