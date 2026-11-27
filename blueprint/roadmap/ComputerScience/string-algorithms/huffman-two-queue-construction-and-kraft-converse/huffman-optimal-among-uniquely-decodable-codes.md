# Huffman codes are optimal among uniquely decodable codes

For symbol weights in any ordered abelian monoid (not necessarily nonnegative, ties allowed), every tree produced by a Huffman construction (repeatedly merge two trees of minimum weight) minimizes the weighted external path length over all full binary code trees. With nonnegative weights its weighted codeword length is at most that of every finite injective uniquely decodable binary code for the same symbols.

## Depends on

- [Huffman's algorithm](../../../InformationTheory/source-coding/huffman-coding/huffman.md)
- [Huffman trees beat every prefix-free code](../../../InformationTheory/source-coding/huffman-coding/huffman-optimal-prefix-free.md)

## Proof depends on

- [Uniquely decodable codes reduce to prefix-free code trees](mcmillan-reduction.md)
- [Huffman trees beat every prefix-free code](../../../InformationTheory/source-coding/huffman-coding/huffman-optimal-prefix-free.md)

## Sources

- D. A. Huffman, "A Method for the Construction of Minimum-Redundancy Codes", Proceedings of the IRE 40(9), 1952.
- B. McMillan, "Two Inequalities Implied by Unique Decipherability", IRE Transactions on Information Theory 2(4), 1956.
- T. M. Cover and J. A. Thomas, "Elements of Information Theory", 2nd ed., Wiley-Interscience, 2006.
