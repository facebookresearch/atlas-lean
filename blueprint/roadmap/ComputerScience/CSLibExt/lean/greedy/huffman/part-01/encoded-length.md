---
article_id: af_eb0c1a564659802cfd2b6ee7
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.HuffmanTree.encodedLength
---

# Encoded Length

The structural encoded-length objective: weighted path length with a one-bit
convention at a lone leaf, so a singleton leaf of weight `w` costs `w`. This agrees
with the public encoder's emitted cost (weight times codeword length, summed over
the weighted leaves) whenever the leaf symbols are unique; see
`HuffmanTree.encodedLength_eq_sum_codeLengths`. For trees with repeated symbols the
encoder resolves each symbol to its first leaf, so on such trees this function is
the structural path cost rather than the emitted encoder cost.

## Depends on

- [Huffman Tree](huffman-tree.md)

## Proof depends on

- [Total Weight](total-weight.md)
- [Weighted Path Length](weighted-path-length.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Greedy.Huffman](../../../../../../../sources/v2/CSLibExt.md)
