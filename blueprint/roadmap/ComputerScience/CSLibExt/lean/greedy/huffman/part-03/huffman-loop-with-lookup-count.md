---
article_id: af_c27e3196e166fc9c1d3175cb
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.huffmanLoopWithLookupCount
---

# Huffman Loop With Lookup Count

Instrumented Huffman execution that reports indexed payload-table reads on
successful runs. Each call to `takeSerial?` performs one `table[serial]?` read.
The count excludes heap operations, table writes (cell clearing and merged-item
insertion), and the terminal `huffmanTableForest` scan.

## Depends on

- [Huffman Priority](../part-02/huffman-priority.md)
- [Huffman Tree](../part-01/huffman-tree.md)
- [Huffman Work Item](../part-02/huffman-work-item.md)
- [Min Heap](../../../data-structures/part-02/binary-heap/part-02/min-heap.md)

## Proof depends on

- [Huffman Loop With Lookup Count Aux](huffman-loop-with-lookup-count-aux.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Greedy.Huffman](../../../../../../../sources/v2/CSLibExt.md)
