---
article_id: af_1dbc326a3292d011e4e5a99e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.huffmanLoop_lookupCount
---

# Huffman Loop lookup Count

A successful loop performs exactly `2 * fuel + 1` indexed payload reads.

## Depends on

- [Huffman Priority](../part-02/huffman-priority.md)
- [Huffman Tree](../part-01/huffman-tree.md)
- [Huffman Work Item](../part-02/huffman-work-item.md)
- [Min Heap](../../../data-structures/part-02/binary-heap/part-02/min-heap.md)
- [Huffman Loop](huffman-loop.md)
- [Huffman Loop With Lookup Count](huffman-loop-with-lookup-count.md)

## Proof depends on

- [Huffman Loop With Lookup Count eq](huffman-loop-with-lookup-count-eq.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Greedy.Huffman](../../../../../../../sources/v2/CSLibExt.md)
