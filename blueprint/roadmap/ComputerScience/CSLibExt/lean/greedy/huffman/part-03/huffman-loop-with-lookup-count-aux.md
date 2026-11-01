---
article_id: af_707774e4ea14c618346adab1
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.huffmanLoopWithLookupCountAux
---

# Huffman Loop With Lookup Count Aux

Accumulator form of `huffmanLoopWithLookupCount`: `count` is the number
of indexed reads already performed, threaded through the recursion so a
successful run uses constant stack in `fuel` just like `huffmanLoop`.
`huffmanLoopWithLookupCount` is the `count = 0` special case, and
`huffmanLoopWithLookupCountAux_eq` is its characteristic equation.

## Depends on

- [Huffman Priority](../part-02/huffman-priority.md)
- [Huffman Tree](../part-01/huffman-tree.md)
- [Huffman Work Item](../part-02/huffman-work-item.md)
- [Min Heap](../../../data-structures/part-02/binary-heap/part-02/min-heap.md)

## Proof depends on

- [Huffman Two Min](../part-02/huffman-two-min.md)
- [Extract Min](../../../data-structures/part-02/binary-heap/part-02/extract-min.md)
- [Push](../../../data-structures/part-02/binary-heap/part-02/push.md)
- [Extract Two Min?](../part-02/extract-two-min.md)
- [Huffman Table Forest](../part-02/huffman-table-forest.md)
- [Take Serial?](../part-02/take-serial.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Greedy.Huffman](../../../../../../../sources/v2/CSLibExt.md)
