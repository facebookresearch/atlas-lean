---
article_id: af_5e2d62389172e56b94b21b48
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.huffmanLoopWithLookupCount_eq
---

# Huffman Loop With Lookup Count eq

Instrumenting the loop preserves its result and, on success, reports two
indexed payload reads per merge followed by one final indexed read.

## Depends on

- [Huffman Priority](../part-02/huffman-priority.md)
- [Huffman Tree](../part-01/huffman-tree.md)
- [Huffman Work Item](../part-02/huffman-work-item.md)
- [Min Heap](../../../data-structures/part-02/binary-heap/part-02/min-heap.md)
- [Huffman Loop](huffman-loop.md)
- [Huffman Loop With Lookup Count](huffman-loop-with-lookup-count.md)

## Proof depends on

- [Huffman Two Min](../part-02/huffman-two-min.md)
- [Extract Min](../../../data-structures/part-02/binary-heap/part-02/extract-min.md)
- [Push](../../../data-structures/part-02/binary-heap/part-02/push.md)
- [Extract Two Min?](../part-02/extract-two-min.md)
- [Huffman Loop With Lookup Count Aux](huffman-loop-with-lookup-count-aux.md)
- [Huffman Table Forest](../part-02/huffman-table-forest.md)
- [Take Serial?](../part-02/take-serial.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Greedy.Huffman](../../../../../../../sources/v2/CSLibExt.md)
