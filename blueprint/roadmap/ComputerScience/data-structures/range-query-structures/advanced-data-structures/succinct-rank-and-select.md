# Succinct rank and select

A bit vector $B$ of length $n$ can be augmented with $o(n)$ additional bits so that, in the word-RAM model with words of $\Theta(\log n)$ bits, $\mathrm{rank}(i)$ (the number of ones among the first $i$ bits) and $\mathrm{select}(j)$ (the position of the $j$-th one) are answered in $O(1)$ time.

## Depends on

- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- G. Jacobson, "Space-efficient static trees and graphs", *Proceedings of the 30th IEEE FOCS*, 1989
- D. R. Clark, *Compact Pat Trees*, PhD thesis, University of Waterloo, 1996
- E. Demaine, *Advanced Data Structures*, MIT 6.851 lecture notes, Spring 2012
