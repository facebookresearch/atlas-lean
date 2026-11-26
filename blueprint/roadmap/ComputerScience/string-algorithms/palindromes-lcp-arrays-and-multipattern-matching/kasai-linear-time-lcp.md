# Kasai et al.: the LCP array in linear time

Given a word $w$ of length $n$ and its suffix array, the algorithm of Kasai, Lee, Arimura, Arikawa and Park visits the suffixes in text order $i = 0, 1, \dots, n-1$, compares the suffix at $i$ with its suffix-array predecessor starting from the previous common-prefix length minus one, and records the result. It computes the LCP array exactly, using $O(n)$ character comparisons, and runs in $O(n + 1)$ word-RAM instructions.

## Proof sketch

The height lemma shows the starting offset is already a common prefix; the running length decreases by at most one per step and never exceeds $n$, so the total number of successful comparisons is at most $2n$.

## Depends on

- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)
- [The LCP array](../../data-structures/tries-and-integer-dictionaries/suffix-array/lcp-array.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [The height lemma for LCP arrays](lcp-height-lemma.md)

## Sources

- T. Kasai, G. Lee, H. Arimura, S. Arikawa and K. Park, "Linear-Time Longest-Common-Prefix Computation in Suffix Arrays and Its Applications", Combinatorial Pattern Matching (CPM 2001), LNCS 2089, Springer, 2001.
