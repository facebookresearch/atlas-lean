# Uniquely decodable codes reduce to prefix-free code trees

Every finite injective binary code that is uniquely decodable (every finite concatenation of codewords has a unique factorization) has codeword lengths satisfying $\sum_i 2^{-\ell_i} \le 1$ (McMillan), and hence there is a full binary code tree, i.e. a prefix-free code, whose codeword for each symbol has length at most the original one. Consequently any lower bound on the expected codeword length of prefix-free codes applies to uniquely decodable codes.

## Proof sketch

McMillan: expand $(\sum_i 2^{-\ell_i})^m$ into a sum over $m$-tuples; unique decodability bounds the number of tuples of total length $L$ by $2^L$, so the power grows at most linearly in $m$. Then apply the constructive Kraft converse and compact the trie into a full tree.

## Depends on

- [Kraft's inequality for prefix codes](../../../InformationTheory/source-coding/kraft-mcmillan-lengths.md)
- [Prefix-free code](../../../InformationTheory/source-coding/prefix-codes/is-prefix-free.md)

## Proof depends on

- [Constructive binary Kraft converse](binary-kraft-converse.md)

## Sources

- B. McMillan, "Two Inequalities Implied by Unique Decipherability", IRE Transactions on Information Theory 2(4), 1956.
- T. M. Cover and J. A. Thomas, "Elements of Information Theory", 2nd ed., Wiley-Interscience, 2006.
