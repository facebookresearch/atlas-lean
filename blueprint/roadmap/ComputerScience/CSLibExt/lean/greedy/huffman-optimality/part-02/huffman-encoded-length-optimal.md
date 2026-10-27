---
article_id: af_8263a4096ce6a8bbf3b270ef
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.huffman_encodedLength_optimal
---

# Huffman encoded Length optimal

The tree returned by `huffman` also minimizes the structural
encoded-length objective, including the one-bit singleton code; by
`HuffmanTree.encodedLength_eq_sum_codeLengths` this is the encoder's emitted
cost whenever the leaf symbols are unique.

## Depends on

- [Huffman Tree](../../huffman/part-01/huffman-tree.md)
- [Admissible](admissible.md)
- [Encoded Length](../../huffman/part-01/encoded-length.md)
- [Huffman](../../huffman/part-03/huffman.md)

## Proof depends on

- [Encoded Length fork](../../huffman/part-01/encoded-length-fork.md)
- [Weighted Leaves](../../huffman/part-01/weighted-leaves.md)
- [Weighted Path Length](../../huffman/part-01/weighted-path-length.md)
- [Huffman optimal](huffman-optimal.md)
- [Huffman weighted Leaves perm](../../huffman/part-03/huffman-weighted-leaves-perm.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Greedy.HuffmanOptimality](../../../../../../../sources/v2/CSLibExt.md)
