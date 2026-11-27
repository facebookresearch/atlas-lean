# Fully functional suffix trees in BWT-runs space

Every text $T$ of length $n$ with $r$ BWT runs has a representation of its suffix tree in $O(r \log\frac{n}{r})$ words that supports most navigation operations of compressed suffix trees (among them parent, first child, next sibling, string depth, suffix link, lowest common ancestor and suffix-array access) in $O(\log\frac{n}{r})$ time each; going to a child by a given letter and level-ancestor queries may cost $O(\log\frac{n}{r}\log n)$.

## Proof sketch

Gagie, Navarro and Prezza use the $O(r)$ text phrases induced by the BWT runs: inside a BWT run, LF maps consecutive rows to consecutive rows, so the differential suffix array $\mathrm{SA}[j] - \mathrm{SA}[j-1]$, the differential inverse suffix array and the differential LCP array repeat across phrases. A block-tree analogue over these phrases gives $O(\log(n/r))$-time access to $\mathrm{SA}$, $\mathrm{ISA}$ and $\mathrm{LCP}$ in $O(r\log(n/r))$ words, and a run-length context-free grammar of size $O(r\log(n/r))$ on the differential LCP array supports the range-minimum and previous/next-smaller-value queries to which suffix tree navigation reduces.

## Depends on

- [Number $r$ of runs in the Burrows–Wheeler transform](../string-attractors-and-repetitiveness-measures/bwt-run-count.md)
- [Suffix tree](../../data-structures/tries-and-integer-dictionaries/suffix-tree/suffix-tree.md)
- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)

## Proof depends on

- [The LCP array](../../data-structures/tries-and-integer-dictionaries/suffix-array/lcp-array.md)
- [The r-index locates in BWT-runs bounded space](r-index-locate.md)

## Sources

- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792.
