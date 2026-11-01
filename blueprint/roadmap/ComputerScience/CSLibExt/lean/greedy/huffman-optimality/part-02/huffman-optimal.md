---
article_id: af_e5659e0543b152113424221f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.huffman_optimal
---

# Huffman optimal

The tree returned by `huffman` globally minimizes weighted path length
among full prefix-code trees with exactly the input's weighted symbols.

## Depends on

- [Huffman Tree](../../huffman/part-01/huffman-tree.md)
- [Admissible](admissible.md)
- [Weighted Path Length](../../huffman/part-01/weighted-path-length.md)
- [Huffman](../../huffman/part-03/huffman.md)

## Proof depends on

- [Huffman merge Trace](huffman-merge-trace.md)
- [Huffman optimal of merge Trace](huffman-optimal-of-merge-trace.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Greedy.HuffmanOptimality](../../../../../../../sources/v2/CSLibExt.md)
