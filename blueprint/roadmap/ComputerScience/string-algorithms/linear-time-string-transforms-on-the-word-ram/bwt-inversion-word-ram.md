# Burrows-Wheeler inversion in O(n + sigma) word-RAM time

For words over the integer alphabet $\{0, \dots, \sigma - 1\}$, there is a deterministic word-RAM program that, given the last column $L$ of length $n$ and the index $I$, computes the tables $C$ and $P$ in $O(n + \sigma)$ instructions and then decodes $w$ by $n$ table lookups in $O(n)$ instructions, so the Burrows-Wheeler transform is inverted in $O(n + \sigma)$ time.

## Depends on

- [Burrows–Wheeler transform](../burrows-wheeler-transform-and-fm-index/bwt.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Table-driven LF-mapping inversion of the Burrows-Wheeler transform](bwt-table-driven-inversion.md)

## Sources

- M. Burrows and D. J. Wheeler, "A Block-sorting Lossless Data Compression Algorithm", technical report 124, Digital Systems Research Center, 1994.
